Require Import util.
Require Import c_util.
Require Import c_monotonic_flow.
Require Import c_geometry.
Set Implicit Arguments.
Open Local Scope CR_scope.

Module one_axis.
Section contents.

  Variables
     (f: Flow CRasCSetoid)
     (finv: CR -> CR -> Time)
     (finv_correct: forall x x', f x (finv x x') == x')
     (fm: mono f)  (a b: Range).

  Let x: Range -> CR := if fm then range_left else range_right.
  Let x': Range -> CR := if fm then range_right else range_left.

  Definition in_r (r: Range) ux: Prop := mle fm (x r) ux /\ mle fm ux (x' r).

  Definition in_range_alt r p: in_range p r <-> in_r p r.
    unfold in_range, in_r, x, x'.
    destruct p. unfold range_left, range_right.
    simpl.
    destruct fm; tauto.
  Qed.

  Add Morphism (@bsm CRasCSetoid CRasCSetoid CRasCSetoid)
    with signature (@eq _) ==> (@cs_eq _) ==> (@cs_eq _) ==> (@cs_eq _)
    as gh_mor.
  Proof. intro. exact (@bsm_mor _ _ _ y y (refl_equal _)). Qed.

  Add Morphism finv with signature (@cs_eq _) ==> (@cs_eq _) ==> (@cs_eq _)
    as finv_wd.
  Proof. intros. apply (inv_wd fm); assumption. Qed.

  Lemma inv_test_guarantees_flow (t: CR):
    finv (x' a) (x b) <= t -> t <= finv (x a) (x' b) ->
    exists xu : CR, in_r a xu /\ in_r b (f xu t).
  Proof with auto.
    intros.
    exists ((if fm then CRmax else CRmin) (f (x b) (-t)) (x a)).
    split.
      split; unfold mle; destruct fm.
            apply CRmax_ub_r.
          apply CRmin_lb_r.
        apply CRmax_lub.
          rewrite (inv_inv fm finv finv_correct) in H.
          rewrite <- (finv_correct (x b) (x' a)).
          apply mildly_increasing...
            intros. rewrite H1. reflexivity. (* hm *)
          apply t12...
        destruct a...
      apply CRmin_glb.
        rewrite (inv_inv fm finv finv_correct) in H.
        rewrite <- (finv_correct (x b) (x' a)).
        apply mildly_decreasing...
          intros. rewrite H1. reflexivity. (* hm *)
        apply t12...
      destruct a...
    split.
      unfold mle.
      destruct fm.
        apply CRle_trans with (f (f (x b) (-t)) t).
          rewrite <- flow_additive...
          rewrite (Radd_comm CR_ring_theory).
          rewrite (Ropp_def CR_ring_theory).
          rewrite flow_zero.
          apply CRle_refl.
        apply (f_le_left fm finv finv_correct).
        apply CRmax_ub_l.
      apply CRle_trans with (f (f (x b) (-t)) t).
        apply (f_le_left fm finv finv_correct).
        apply CRmin_lb_l.
      clear H H0.
      rewrite <- flow_additive.
      rewrite (Radd_comm CR_ring_theory).
      rewrite (Ropp_def CR_ring_theory).
      rewrite flow_zero.
      apply CRle_refl.
    assert (x' b == f (f (x' b) (-t)) t).
      rewrite <- flow_additive.
      rewrite (Radd_comm CR_ring_theory).
      rewrite (Ropp_def CR_ring_theory).
      rewrite flow_zero...
      reflexivity.
    unfold mle.
    destruct fm.
      rewrite H1.
      apply (f_le_left fm finv finv_correct).
      apply CRmax_lub.
        apply (f_le_left fm finv finv_correct).
        destruct b...
      rewrite <- (finv_correct (x' b) (x a)).
      apply mildly_increasing...
        intros. rewrite H2. reflexivity. (* hm *)
      rewrite (inv_inv fm finv finv_correct).
      apply t8...
    rewrite H1.
    apply (f_le_left fm finv finv_correct).
    apply CRmin_glb.
      apply (f_le_left fm finv finv_correct).
      destruct b...
    rewrite <- (finv_correct (x' b) (x a)).
    apply mildly_decreasing...
      intros. rewrite H2. reflexivity. (* hm *)
    rewrite (inv_inv fm finv finv_correct).
    apply t8...
  Qed.

End contents.
End one_axis.

Section contents.

  Variables
     (fx fy: Flow CRasCSetoid)
     (finvx finvy: CR -> CR -> Time)
     (finvx_correct: forall x x', fx x (finvx x x') == x')
     (finvy_correct: forall y y', fy y (finvy y y') == y')
     (fxm: mono fx) (fym: mono fy) (a b: Square).

  Definition f (p: Point) (t: Time): Point := (fx (fst p) t, fy (snd p) t).

  Let x  (s: Square): CR := (if fxm then range_left  else range_right) (fst s).
  Let x' (s: Square): CR := (if fxm then range_right else range_left ) (fst s).
  Let y  (s: Square): CR := (if fym then range_left  else range_right) (snd s).
  Let y' (s: Square): CR := (if fym then range_right else range_left ) (snd s).

  Let in_x (s: Square) ux: Prop := mle fxm (x s) ux /\ mle fxm ux (x' s).
  Let in_y (s: Square) uy: Prop := mle fym (y s) uy /\ mle fym uy (y' s).

  Let mle_x_x' s: mle fxm (x s) (x' s).
  Proof. subst x x'. intros. destruct s. destruct r. destruct fxm; auto. Qed.

  Let mle_y_y' s: mle fym (y s) (y' s).
  Proof. subst y y'. intros. destruct s. destruct r0. destruct fym; auto. Qed.

  Hint Immediate mle_x_x' mle_y_y'.

  Let in_s s (p: Point): Prop :=
    in_x s (fst p) /\ in_y s (snd p).
    (* expressed in terms of the mono accessors, makes reasoning easier *)

  Definition in_square_alt s p: in_square p s <-> in_s s p.
    unfold in_square, in_s, in_x, in_y.
    destruct s. destruct p. destruct r. destruct r0.
    subst x x' y y'.
    simpl. unfold in_range.
    destruct fxm; destruct fym; tauto.
  Qed.

  Let in_x_x s: in_x s (x s).
  Proof. subst in_x. split. apply mle_refl. apply mle_x_x'. Qed.
  Let in_x_x' s: in_x s (x' s).
  Proof. subst in_x. split. apply mle_x_x'. apply mle_refl. Qed.
  Let in_y_y s: in_y s (y s).
  Proof. subst in_y. split. apply mle_refl. apply mle_y_y'. Qed.
  Let in_y_y' s: in_y s (y' s).
  Proof. subst in_y. split. apply mle_y_y'. apply mle_refl. Qed.

  Hint Immediate in_x_x in_x_x' in_y_y in_y_y'.

  Definition ideal: Prop :=
    exists p: Point, in_square p a /\
    exists t: Time, '0 <= t /\ in_square (f p t) b.
      (* unaware of invariants *)

  Definition naive_ideal: Prop :=
    exists p: Point, in_square p a /\
    exists t: Time, in_square (f p t) b.
    (* naive because it doesn't require 0<=t *)

  Definition naive_decideable: Prop :=
    finvx (x' a) (x b) <= finvy (y a) (y' b) /\
    finvy (y' a) (y b) <= finvx (x a) (x' b).
    (* naive in the same way *)

  (* While these naive conditions aren't suitable for actual use,
   they are neatly equivalent. *)

  Lemma naive_ideal_implies_naive_decideable: naive_ideal -> naive_decideable.
  Proof with auto with real.
    unfold naive_ideal, naive_decideable.
    intros.
    destruct H. destruct H. destruct H0.
    set (fst (in_square_alt a x0) H).
      clearbody i. clear H. rename i into H.
    set (fst (in_square_alt b (f x0 x1)) H0).
      clearbody i. clear H0. rename i into H0.
    destruct H. destruct H0.
    rename x1 into t. destruct x0. rename c into ux. rename c0 into uy.
    destruct H. destruct H1. destruct H0. destruct H2.
    simpl in *.
    set (snd (inv_nonneg fxm finvx finvx_correct _ _) H).
    set (snd (inv_nonneg fxm finvx finvx_correct _ _) H0).
    set (snd (inv_nonneg fym finvy finvy_correct _ _) H1).
    set (snd (inv_nonneg fym finvy finvy_correct _ _) H2).
    set (snd (inv_nonneg fxm finvx finvx_correct _ _) H3).
    set (snd (inv_nonneg fym finvy finvy_correct _ _) H4).
    set (snd (inv_nonneg fxm finvx finvx_correct _ _) H5).
    set (snd (inv_nonneg fym finvy finvy_correct _ _) H6).
    clearbody c c0 c1 c2 c3 c4 c5 c6.
    split; apply CRle_trans with t.
          rewrite <- (inv_correct' fxm finvx finvx_correct ux t).
          rewrite (inv_plus fxm finvx finvx_correct ux (x' a) (fx ux t)).
          rewrite (inv_plus fxm finvx finvx_correct (x' a) (x b) (fx ux t)).
          rewrite <- (Radd_0_l CR_ring_theory (finvx (x' a) (x b))) at 1.
          apply t9...
          rewrite <- (Radd_0_l CR_ring_theory (finvx (x' a) (x b))) at 1.
          rewrite (Radd_comm CR_ring_theory).
          apply t9...
          apply CRle_refl.
        rewrite <- (inv_correct' fym finvy finvy_correct uy t).
        rewrite (inv_plus fym finvy finvy_correct (y a) uy (y' b)).
        rewrite (inv_plus fym finvy finvy_correct uy (fy uy t) (y' b)).
        rewrite <- (Radd_0_l CR_ring_theory (finvy uy (fy uy t))) at 1.
        apply t9...
        rewrite <- (Radd_0_l CR_ring_theory (finvy uy (fy uy t))) at 1.
        rewrite (Radd_comm CR_ring_theory).
        apply t9...
        apply CRle_refl.
      rewrite <- (inv_correct' fym finvy finvy_correct uy t).
      rewrite (inv_plus fym finvy finvy_correct uy (y' a) (fy uy t)).
      rewrite (inv_plus fym finvy finvy_correct (y' a) (y b) (fy uy t)).
      rewrite <- (Radd_0_l CR_ring_theory (finvy (y' a) (y b))) at 1.
      apply t9...
      rewrite <- (Radd_0_l CR_ring_theory (finvy (y' a) (y b))) at 1.
      rewrite (Radd_comm CR_ring_theory).
      apply t9...
      apply CRle_refl.
    rewrite <- (inv_correct' fxm finvx finvx_correct ux t).
    rewrite (inv_plus fxm finvx finvx_correct (x a) ux (x' b)).
    rewrite (inv_plus fxm finvx finvx_correct ux (fx ux t) (x' b)).
    rewrite <- (Radd_0_l CR_ring_theory (finvx ux (fx ux t))) at 1.
    apply t9...
    rewrite <- (Radd_0_l CR_ring_theory (finvx ux (fx ux t))) at 1.
    rewrite (Radd_comm CR_ring_theory).
    apply t9...
    apply CRle_refl.
  Qed.

  Corollary ideal_implies_naive_decideable: ideal -> naive_decideable.
  Proof.
    intro. apply naive_ideal_implies_naive_decideable.
    destruct H. destruct H. destruct H0. destruct H0.
    unfold naive_ideal. eauto.
  Qed.

  Hint Resolve mle_refl.

  Let finvx_ax'_bx_le_finvx_ax_bx':
    finvx (x' a) (x b) <= finvx (x a) (x' b).
  Proof with auto.
    apply CRle_trans with (finvx (x' a) (x' b)).
      apply (inv_le fxm finvx finvx_correct).
      destruct fxm; apply mle_x_x'.
    apply (inv_le_left fxm finvx)...
  Qed.

  Let finvy_ay'_by_le_finvy_ay_by':
    finvy (y' a) (y b) <= finvy (y a) (y' b).
  Proof with auto.
    apply CRle_trans with (finvy (y' a) (y' b)).
      apply (inv_le fym finvy finvy_correct).
      destruct fym; apply mle_y_y'.
    apply (inv_le_left fym finvy)...
  Qed.

  Lemma naive_decideable_implies_naive_ideal:
    naive_decideable -> naive_ideal.
  Proof with auto with real.
    intros.
    destruct H.
    set (t := CRmin (finvx (x a) (x' b)) (finvy (y a) (y' b))).
    unfold naive_ideal.
    assert (finvx (x' a) (x b) <= t /\ t <= finvx (x a) (x' b)).
      unfold t.
      split.
        apply CRmin_glb...
      apply CRmin_lb_l.
    assert (finvy (y' a) (y b) <= t /\ t <= finvy (y a) (y' b)).
      unfold t.
      split.
        apply CRmin_glb...
      apply CRmin_lb_r.
    assert (exists xu, in_x a xu /\ in_x b (fx xu t)).
      destruct H1. destruct H2.
      apply (one_axis.inv_test_guarantees_flow finvx finvx_correct fxm)...
    assert (exists yu, in_y a yu /\ in_y b (fy yu t)).
      destruct H1. destruct H2.
      apply (one_axis.inv_test_guarantees_flow finvy finvy_correct fym)...
    destruct H3.
    destruct H4.
    rename x0 into xu. rename x1 into yu.
    exists (xu, yu).
    set in_square_alt. clearbody i.
    subst in_s in_x in_y.
    simpl in *.
    destruct H3. destruct H4. destruct H3. destruct H4.
    destruct H5. destruct H6.
    split...
    destruct (i a (xu, yu)). destruct a. simpl in *...
    exists t...
    destruct (i b (f (xu, yu) t)). destruct b. simpl in *...
  Qed.

  Theorem naive_conditions_equivalent: naive_decideable <-> naive_ideal.
    split.
      apply naive_decideable_implies_naive_ideal.
    apply naive_ideal_implies_naive_decideable.
  Qed.

  Definition strong_decideable: Prop :=
    naive_decideable /\ mle fxm (x' a) (x' b) /\ mle fym (y' a) (y' b).
      (* This is strong enough to imply ideal, but too strong
        to get the reverse implication. (The latter claim is not
        yet proved.) *)

  Lemma strong_decideable_implies_ideal: strong_decideable -> ideal.
  Proof with auto with real.
    intros.
    destruct H. destruct H. destruct H0.
    set (t := CRmin (finvx (x a) (x' b)) (finvy (y a) (y' b))).

    assert (finvx (x' a) (x b) <= t /\ t <= finvx (x a) (x' b)).
      unfold t.
      split.
        apply CRmin_glb...
      apply CRmin_lb_l.
    assert (finvy (y' a) (y b) <= t /\ t <= finvy (y a) (y' b)).
      unfold t.
      split.
        apply CRmin_glb...
      apply CRmin_lb_r.
    assert (exists xu, in_x a xu /\ in_x b (fx xu t)).
      destruct H3. destruct H4.
      apply (one_axis.inv_test_guarantees_flow finvx finvx_correct fxm)...
    assert (exists yu, in_y a yu /\ in_y b (fy yu t)).
      destruct H3. destruct H4.
      apply (one_axis.inv_test_guarantees_flow finvy finvy_correct fym)...
    destruct H5. destruct H6.
    unfold ideal.
    rename x0 into xu. rename x1 into yu.
    exists (xu, yu).
    subst in_x in_y.
    simpl in H5, H6.
    destruct H5. destruct H6. destruct H5. destruct H6.
    destruct H7. destruct H8.
    split.
      destruct (in_square_alt a (xu, yu)).
      apply H14.
      split...
    exists t.
    split.
      unfold t.
      admit.
      (*

      unfold CRmin.
      destruct H3. destruct H4.
      destruct (Rle_dec (finvx (x a) (x' b)) (finvy (y a) (y' b))).
        destruct (inv_nonneg fxm fxf finvx finvx_correct (x a) (x' b)).
        apply H16.
        apply mle_trans with (x' a)...
      destruct (inv_nonneg fym fyf finvy finvy_correct (y a) (y' b)).
      apply H16.
      apply mle_trans with (y' a)...
      *)
    destruct (in_square_alt b (f (xu, yu) t)).
    apply H14.
    split...
  Qed.

  Definition practical_decideable: Prop :=
    naive_decideable /\ mle fxm (x a) (x' b) /\ mle fym (y a) (y' b).
        (* This is weak enough to be implied by ideal, but not strong
          enough to get the reverse implication. (The latter claim is not
          yet proved.) For now, it's an acceptable compromise. *)

    (* Todo: can we define a decideable condition equivalent
     to (non-naive) ideal? *)


  Lemma ideal_implies_practical_decideable:
    ideal -> practical_decideable.
  Proof with auto with real.
    unfold ideal, practical_decideable.
    split.
      apply ideal_implies_naive_decideable...
    destruct H. destruct H. destruct H0. destruct H0.
    set (fst (in_square_alt a x0) H). clearbody i. clear H. rename i into H.
    set (fst (in_square_alt b (f x0 x1)) H1). clearbody i. clear H1. rename i into H1.
    destruct x0. rename x1 into t. rename c into ux. rename c0 into uy.
    destruct H. destruct H1. simpl in *.
    destruct H. destruct H2. destruct H1. destruct H3.
    split.
      apply mle_trans with ux...
      apply mle_trans with (fx ux t)...
      apply mle_flow...
    apply mle_trans with uy...
    apply mle_trans with (fy uy t)...
    apply mle_flow...
  Qed.

  Lemma practical_decideable_implies_naive_ideal:
    practical_decideable -> naive_ideal.
  Proof.
    unfold practical_decideable.
    intros.
    apply naive_decideable_implies_naive_ideal.
    destruct H. assumption.
  Qed.

  Definition naive_dec eps (_ : unit) : bool :=
    CRle_dec eps (finvx (x' a) (x b), finvy (y a) (y' b)) &&
    CRle_dec eps (finvy (y' a) (y b), finvx (x a) (x' b)).

  Lemma over_naive_dec eps : naive_dec eps >=> fun _ => naive_decideable.
  Proof.
    intros eps q n_d [o1 o2]. unfold naive_dec in n_d.
    band_discr; estim (over_CRle eps).
  Qed.

  Definition practical_dec eps (_ : unit) : bool :=
    naive_dec eps () && 
    (if fxm then CRle_dec eps (x a, x' b) else CRle_dec eps (x' b, x a)) &&
    (if fym then CRle_dec eps (y a, y' b) else CRle_dec eps (y' b, y a)).

  Lemma over_practical_dec eps : 
    practical_dec eps >=> fun _ => practical_decideable.
  Proof with auto.
    intros eps q n_d [nd [o1 o2]]. unfold practical_dec in n_d.
    band_discr. bool_solver.
    apply (over_true () (over_naive_dec eps))...
    generalize o1. case fxm; intros; estim (over_CRle eps).
    generalize o2. case fym; intros; estim (over_CRle eps).
  Qed.

End contents.
