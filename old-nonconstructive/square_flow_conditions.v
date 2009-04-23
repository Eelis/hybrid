Require Import Coq.Reals.Reals.
Require Import Fourier.
Require Import util.
Require Import flow.
Require Import geometry.
Require Import monotonic_flow.
Set Implicit Arguments.
Open Local Scope R_scope.

Module one_axis.
Section contents.

  Variables
     (f: Flow R)
     (finv: R -> R -> Time)
     (finv_correct: forall x x', f x (finv x x') = x')
     (fm: mono f)  (a b: Range).

  Let x: Range -> R := if fm then range_left else range_right.
  Let x': Range -> R := if fm then range_right else range_left.

  Definition in_r (r: Range) ux: Prop := mle fm (x r) ux /\ mle fm ux (x' r).

  Definition in_range_alt r p: in_range p r <-> in_r p r.
    unfold in_range, in_r, x, x'.
    destruct p. unfold range_left, range_right.
    simpl.
    destruct fm; tauto.
  Qed.

  Lemma inv_test_guarantees_flow (t: R):
    finv (x' a) (x b) <= t <= finv (x a) (x' b) ->
    exists xu : R, in_r a xu /\ in_r b (f xu t).
  Proof with auto with real.
      (* this proof is way longer than the one below, but this one
       is more constructive in that it instantiates the exists with
       Rmin/Rmax instead of doing case distinction on a </=/> decision. *)
    intros.
    destruct H.
    exists ((if fm then Rmax else Rmin) (f (x b) (-t)) (x a)).
    split.
      split.
        destruct fm; simpl.
          apply RmaxLess2.
        unfold x.
        apply Rmin_r.
      destruct fm; simpl.
        apply Rmax_le...
          rewrite (inv_inv fm finv finv_correct) in H.
          assert (-t <= finv (x b) (x' a)) by fourier.
          rewrite <- (finv_correct (x b) (x' a)).
          apply mildly_increasing...
        destruct a...
      apply Rmin_le...
        rewrite (inv_inv fm finv finv_correct) in H.
        assert (-t <= finv (x b) (x' a)) by fourier.
        rewrite <- (finv_correct (x b) (x' a)).
        apply mildly_decreasing...
      destruct a...
    split.
      destruct fm; simpl.
        apply Rle_trans with (f (f (x b) (-t)) t).
          rewrite <- flow_additive...
          rewrite Rplus_opp_l.
          rewrite flow_zero...
        apply (f_le_left fm finv finv_correct (f (x b) (-t))
          (Rmax (f (x b) (- t)) (x a)) t).
        apply RmaxLess1.
      apply Rle_trans with (f (f (x b) (-t)) t).
        apply (f_le_left fm finv finv_correct
          (Rmin (f (x b) (- t)) (x a)) (f (x b) (-t)) t).
        apply Rmin_l.
      clear H H0.
      rewrite <- flow_additive.
      rewrite Rplus_opp_l.
      rewrite flow_zero...
    replace (x' b) with (f (f (x' b) (-t)) t).
      destruct fm; simpl.
        apply (f_le_left fm finv finv_correct
          (Rmax (f (x b) (-t)) (x a)) (f (x' b) (-t)) t).
        apply Rmax_le.
          apply (f_le_left fm finv finv_correct (x b) (x' b) (-t)).
          destruct b...
        rewrite <- (finv_correct (x' b) (x a)).
        apply mildly_increasing...
        rewrite (inv_inv fm finv finv_correct).
        fourier.
      apply (f_le_left fm finv finv_correct
        (f (x' b) (-t)) (Rmin (f (x b) (-t)) (x a)) t).
      apply Rmin_le.
        apply (f_le_left fm finv finv_correct (x' b) (x b) (-t)).
        destruct b...
      rewrite <- (finv_correct (x' b) (x a)).
      apply mildly_decreasing...
      rewrite (inv_inv fm finv finv_correct).
      fourier.
    rewrite <- flow_additive.
    rewrite Rplus_opp_l.
    rewrite flow_zero...
  Qed.

  Let in_x_x s: in_r s (x s).
  Proof.
    unfold in_r. split. apply mle_refl.
    destruct s. destruct fm; auto with real.
  Qed.

  Let in_x_x' s: in_r s (x' s).
  Proof.
    unfold in_r. split.
    destruct s.
      clear in_x_x.
      destruct fm; auto with real.
    apply mle_refl.
  Qed.

  Lemma inv_test_guarantees_flow' (t: R):
    finv (x' a) (x b) <= t <= finv (x a) (x' b) ->
    exists xu : R, in_r a xu /\ in_r b (f xu t).
  Proof with auto with real.
    intros.
    destruct H.
    destruct (Rle_lt_dec t (finv (x' a) (x' b))).
      exists (x' a).
      split...
      split; [replace (x b) with (f (x' a) (finv (x' a) (x b)))
        | replace (x' b) with (f (x' a) (finv (x' a) (x' b)))]; try apply mono_opp...
    exists (f (x' b) (-t)).
    unfold in_r. simpl.
    split.
      split.
        replace (x a) with (f (x' b) (finv (x' b) (x a)))...
        apply mono_opp.
        rewrite (inv_inv fm finv finv_correct (x' b) (x a))...
      replace (x' a) with (f (x' b) (finv (x' b) (x' a)))...
      apply mono_opp.
      rewrite (inv_inv fm finv finv_correct (x' b) (x' a))...
    rewrite <- flow_additive...
    replace (- t + t) with 0...
    rewrite flow_zero...
    destruct b. destruct x0.
    clear in_x_x in_x_x'.
    subst x x'.
    clear H H0 r.
    simpl in r0.
    split; destruct fm; simpl...
  Qed.

End contents.
End one_axis.

Section contents.

  Variables
     (fx fy: Flow R)
     (finvx finvy: R -> R -> Time)
     (finvx_correct: forall x x', fx x (finvx x x') = x')
     (finvy_correct: forall y y', fy y (finvy y y') = y')
     (fxm: mono fx) (fym: mono fy) (a b: Square).

  Definition f (p: Point) (t: Time): Point := (fx (fst p) t, fy (snd p) t).

  Let x  (s: Square): R := (if fxm then range_left  else range_right) (fst s).
  Let x' (s: Square): R := (if fxm then range_right else range_left ) (fst s).
  Let y  (s: Square): R := (if fym then range_left  else range_right) (snd s).
  Let y' (s: Square): R := (if fym then range_right else range_left ) (snd s).

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
    exists t: Time, 0 <= t /\ in_square (f p t) b.
      (* unaware of invariants *)

  Definition naive_ideal: Prop :=
    exists p: Point, in_square p a /\ exists t: Time, in_square (f p t) b.
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
    set (conj_fst (in_square_alt a x0) H).
      clearbody i. clear H. rename i into H.
    set (conj_fst (in_square_alt b (f x0 x1)) H0).
      clearbody i. clear H0. rename i into H0.
    destruct H. destruct H0.
    rename x1 into t. destruct x0. rename r into ux. rename r0 into uy.
    destruct H. destruct H1. destruct H0. destruct H2.
    simpl in *.
    set (conj_snd (inv_nonneg fxm finvx finvx_correct _ _) H).
    set (conj_snd (inv_nonneg fxm finvx finvx_correct _ _) H0).
    set (conj_snd (inv_nonneg fym finvy finvy_correct _ _) H1).
    set (conj_snd (inv_nonneg fym finvy finvy_correct _ _) H2).
    set (conj_snd (inv_nonneg fxm finvx finvx_correct _ _) H3).
    set (conj_snd (inv_nonneg fym finvy finvy_correct _ _) H4).
    set (conj_snd (inv_nonneg fxm finvx finvx_correct _ _) H5).
    set (conj_snd (inv_nonneg fym finvy finvy_correct _ _) H6).
    clearbody r r0 r1 r2 r3 r4 r5 r6.
    split; apply Rle_trans with t.
          rewrite <- (inv_correct' fxm finvx finvx_correct ux t).
          rewrite (inv_plus fxm finvx finvx_correct ux (x' a) (fx ux t)).
          rewrite (inv_plus fxm finvx finvx_correct (x' a) (x b) (fx ux t)).
          fourier.
        rewrite <- (inv_correct' fym finvy finvy_correct uy t).
        rewrite (inv_plus fym finvy finvy_correct (y a) uy (y' b)).
        rewrite (inv_plus fym finvy finvy_correct uy (fy uy t) (y' b)).
        fourier.
      rewrite <- (inv_correct' fym finvy finvy_correct uy t).
      rewrite (inv_plus fym finvy finvy_correct uy (y' a) (fy uy t)).
      rewrite (inv_plus fym finvy finvy_correct (y' a) (y b) (fy uy t)).
      fourier.
    rewrite <- (inv_correct' fxm finvx finvx_correct ux t).
    rewrite (inv_plus fxm finvx finvx_correct (x a) ux (x' b)).
    rewrite (inv_plus fxm finvx finvx_correct ux (fx ux t) (x' b)).
    fourier.
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
    apply Rle_trans with (finvx (x' a) (x' b)).
      apply (inv_le fxm finvx finvx_correct).
      destruct fxm; apply mle_x_x'.
    apply (inv_le_left fxm finvx finvx_correct).
    destruct fxm; apply mle_x_x'.
  Qed.

  Let finvy_ay'_by_le_finvy_ay_by':
    finvy (y' a) (y b) <= finvy (y a) (y' b).
  Proof with auto.
    apply Rle_trans with (finvy (y' a) (y' b)).
      apply (inv_le fym finvy finvy_correct).
      destruct fym; apply mle_y_y'.
    apply (inv_le_left fym finvy finvy_correct).
    destruct fym; apply mle_y_y'.
  Qed.

  Lemma naive_decideable_implies_naive_ideal:
    naive_decideable -> naive_ideal.
  Proof with auto with real.
    intros.
    destruct H.
    set (t := Rmin (finvx (x a) (x' b)) (finvy (y a) (y' b))).
    unfold naive_ideal.
    assert (finvx (x' a) (x b) <= t <= finvx (x a) (x' b)).
      split.
        unfold t.
        unfold Rmin.
        destruct (Rle_dec (finvx (x a) (x' b)) (finvy (y a) (y' b)))...
      apply Rmin_l.
    assert (finvy (y' a) (y b) <= t <= finvy (y a) (y' b)).
      split.
        unfold t.
        unfold Rmin.
        destruct (Rle_dec (finvx (x a) (x' b)) (finvy (y a) (y' b)))...
      apply Rmin_r.
    assert (exists xu, in_x a xu /\ in_x b (fx xu t)).
      apply (one_axis.inv_test_guarantees_flow finvx finvx_correct fxm)...
    assert (exists yu, in_y a yu /\ in_y b (fy yu t)).
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
      destruct (i a (xu, yu))...
    exists t...
    destruct (i b (f (xu, yu) t))...
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
    set (t := Rmin (finvx (x a) (x' b)) (finvy (y a) (y' b))).
    assert (finvx (x' a) (x b) <= t <= finvx (x a) (x' b)).
      split.
        unfold t.
        unfold Rmin.
        destruct (Rle_dec (finvx (x a) (x' b)) (finvy (y a) (y' b)))...
      apply Rmin_l.
    assert (finvy (y' a) (y b) <= t <= finvy (y a) (y' b)).
      split.
        unfold t.
        unfold Rmin.
        destruct (Rle_dec (finvx (x a) (x' b)) (finvy (y a) (y' b)))...
      apply Rmin_r.
    assert (exists xu, in_x a xu /\ in_x b (fx xu t)).
      apply (one_axis.inv_test_guarantees_flow finvx finvx_correct fxm)...
    assert (exists yu, in_y a yu /\ in_y b (fy yu t)).
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
      unfold Rmin.
      destruct H3. destruct H4.
      destruct (Rle_dec (finvx (x a) (x' b)) (finvy (y a) (y' b))).
        destruct (inv_nonneg fxm finvx finvx_correct (x a) (x' b)).
        apply H16.
        apply mle_trans with (x' a)...
      destruct (inv_nonneg fym finvy finvy_correct (y a) (y' b)).
      apply H16.
      apply mle_trans with (y' a)...
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
    set (conj_fst (in_square_alt a x0) H). clearbody i. clear H. rename i into H.
    set (conj_fst (in_square_alt b (f x0 x1)) H1). clearbody i. clear H1. rename i into H1.
    destruct x0. rename x1 into t. rename r into ux. rename r0 into uy.
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
  Proof with auto with real.
    unfold practical_decideable.
    intros.
    apply naive_decideable_implies_naive_ideal.
    firstorder.
  Qed.

  Definition decide_naive: { naive_decideable } + { ~ naive_decideable }.
  Proof.
    unfold naive_decideable.
    subst x x' y y'.
    destruct a. destruct b.
    apply and_dec; apply Rle_dec.
  Defined.

  Definition decide_practical:
    { practical_decideable } + { ~ practical_decideable }.
  Proof.
    unfold practical_decideable.
    apply and_dec. apply decide_naive.
    apply and_dec; [destruct fxm | destruct fym]; apply Rle_dec.
  Defined.

End contents.
