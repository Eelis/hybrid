Require Import Coq.Reals.Reals.
Require Import Fourier.
Require Import util.
Require Import geometry.
Require Import monotonic_flow.
Set Implicit Arguments.
Open Local Scope R_scope.

Section contents.

  Variables
     (fx fy: R -> Time -> R)
     (fxf: concrete.flows fx) (fyf: concrete.flows fy)
     (finvx finvy: R -> R -> Time)
     (finvx_correct: forall x x', fx x (finvx x x') = x')
     (finvy_correct: forall y y', fy y (finvy y y') = y')
     (fxm: mono fx) (fym: mono fy) (a b: Square).

  Definition f (p: Point) (t: Time): Point := (fx (fst p) t, fy (snd p) t).

  Let x  (s: Square): R := let (r, _, r', _, _, _) := s in if fxm then r  else r'.
  Let x' (s: Square): R := let (r, _, r', _, _, _) := s in if fxm then r' else r.
  Let y  (s: Square): R := let (_, r, _, r', _, _) := s in if fym then r  else r'.
  Let y' (s: Square): R := let (_, r, _, r', _, _) := s in if fym then r' else r.

  Let in_x (s: Square) ux: Prop := mle fxm (x s) ux /\ mle fxm ux (x' s).
  Let in_y (s: Square) uy: Prop := mle fym (y s) uy /\ mle fym uy (y' s).

  Let mle_x_x' s: mle fxm (x s) (x' s).
  Proof. subst x x'. destruct s. destruct fxm; auto. Qed.
  Let mle_y_y' s: mle fym (y s) (y' s).
  Proof. subst y y'. destruct s. destruct fym; auto. Qed.

  Hint Immediate mle_x_x' mle_y_y'.

  Let in_s s (p: Point): Prop :=
    in_x s (fst p) /\ in_y s (snd p).
    (* expressed in terms of the mono accessors, makes reasoning easier *)

  Definition in_square_alt s p: in_square p s <-> in_s s p.
    unfold in_square, in_s, in_x, in_y.
    destruct s. destruct p. simpl.
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
    set (conj_snd (inv_nonneg fxm fxf finvx finvx_correct _ _) H).
    set (conj_snd (inv_nonneg fxm fxf finvx finvx_correct _ _) H0).
    set (conj_snd (inv_nonneg fym fyf finvy finvy_correct _ _) H1).
    set (conj_snd (inv_nonneg fym fyf finvy finvy_correct _ _) H2).
    set (conj_snd (inv_nonneg fxm fxf finvx finvx_correct _ _) H3).
    set (conj_snd (inv_nonneg fym fyf finvy finvy_correct _ _) H4).
    set (conj_snd (inv_nonneg fxm fxf finvx finvx_correct _ _) H5).
    set (conj_snd (inv_nonneg fym fyf finvy finvy_correct _ _) H6).
    clearbody r r0 r1 r2 r3 r4 r5 r6.
    split; apply Rle_trans with t.
          rewrite <- (inv_correct' fxm finvx finvx_correct ux t).
          rewrite (inv_plus fxm fxf finvx finvx_correct ux (x' a) (fx ux t)).
          rewrite (inv_plus fxm fxf finvx finvx_correct (x' a) (x b) (fx ux t)).
          fourier.
        rewrite <- (inv_correct' fym finvy finvy_correct uy t).
        rewrite (inv_plus fym fyf finvy finvy_correct (y a) uy (y' b)).
        rewrite (inv_plus fym fyf finvy finvy_correct uy (fy uy t) (y' b)).
        fourier.
      rewrite <- (inv_correct' fym finvy finvy_correct uy t).
      rewrite (inv_plus fym fyf finvy finvy_correct uy (y' a) (fy uy t)).
      rewrite (inv_plus fym fyf finvy finvy_correct (y' a) (y b) (fy uy t)).
      fourier.
    rewrite <- (inv_correct' fxm finvx finvx_correct ux t).
    rewrite (inv_plus fxm fxf finvx finvx_correct (x a) ux (x' b)).
    rewrite (inv_plus fxm fxf finvx finvx_correct ux (fx ux t) (x' b)).
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
    apply (inv_le_left fxm fxf finvx finvx_correct).
    destruct fxm; apply mle_x_x'.
  Qed.

  Let finvy_ay'_by_le_finvy_ay_by':
    finvy (y' a) (y b) <= finvy (y a) (y' b).
  Proof with auto.
    apply Rle_trans with (finvy (y' a) (y' b)).
      apply (inv_le fym finvy finvy_correct).
      destruct fym; apply mle_y_y'.
    apply (inv_le_left fym fyf finvy finvy_correct).
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
      intros.
      destruct H1. destruct H2.
      destruct (Rle_lt_dec t (finvx (x' a) (x' b))).
        exists (x' a).
        split...
        subst in_x.
        simpl.
        split; [replace (x b) with (fx (x' a) (finvx (x' a) (x b)))
          | replace (x' b) with (fx (x' a) (finvx (x' a) (x' b)))]; auto;
            apply mono_opp...
      exists (fx (x' b) (-t)).
      subst in_x. simpl.
      split.
        split.
          replace (x a) with (fx (x' b) (finvx (x' b) (x a)))...
          apply mono_opp.
          rewrite (inv_inv fxm fxf finvx finvx_correct (x' b) (x a))...
        replace (x' a) with (fx (x' b) (finvx (x' b) (x' a)))...
        apply mono_opp.
        rewrite (inv_inv fxm fxf finvx finvx_correct (x' b) (x' a))...
      rewrite <- (concrete.flow_additive fxf)...
      replace (- t + t) with 0...
      rewrite (concrete.flow_zero fxf)...
    assert (exists yu, in_y a yu /\ in_y b (fy yu t)).
      intros.
      destruct H1. destruct H2.
      destruct (Rle_lt_dec t (finvy (y' a) (y' b))).
        exists (y' a).
        split...
        subst in_y.
        simpl.
        split; [replace (y b) with (fy (y' a) (finvy (y' a) (y b)))
          | replace (y' b) with (fy (y' a) (finvy (y' a) (y' b)))]; auto;
            apply mono_opp...
      exists (fy (y' b) (-t)).
      subst in_y.
      split.
        split.
          replace (y a) with (fy (y' b) (finvy (y' b) (y a)))...
          apply mono_opp.
          rewrite (inv_inv fym fyf finvy finvy_correct (y' b) (y a))...
        replace (y' a) with (fy (y' b) (finvy (y' b) (y' a)))...
        apply mono_opp.
        rewrite (inv_inv fym fyf finvy finvy_correct (y' b) (y' a))...
      rewrite <- (concrete.flow_additive fyf)...
      replace (- t + t) with 0...
      rewrite (concrete.flow_zero fyf)...
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
      intros.
      destruct H3. destruct H4.
      destruct (Rle_lt_dec t (finvx (x' a) (x' b))).
        exists (x' a).
        split...
        subst in_x.
        simpl.
        split; [replace (x b) with (fx (x' a) (finvx (x' a) (x b)))
          | replace (x' b) with (fx (x' a) (finvx (x' a) (x' b)))]; auto;
            apply mono_opp...
      exists (fx (x' b) (-t)).
      subst in_x.
      split.
        split.
          replace (x a) with (fx (x' b) (finvx (x' b) (x a)))...
          apply mono_opp.
          rewrite (inv_inv fxm fxf finvx finvx_correct (x' b) (x a))...
        replace (x' a) with (fx (x' b) (finvx (x' b) (x' a)))...
        apply mono_opp.
        rewrite (inv_inv fxm fxf finvx finvx_correct (x' b) (x' a))...
      rewrite <- (concrete.flow_additive fxf)...
      replace (- t + t) with 0...
      rewrite (concrete.flow_zero fxf)...
    assert (exists yu, in_y a yu /\ in_y b (fy yu t)).
      intros.
      destruct H3. destruct H4.
      destruct (Rle_lt_dec t (finvy (y' a) (y' b))).
        exists (y' a).
        split...
        subst in_y.
        simpl.
        split; [replace (y b) with (fy (y' a) (finvy (y' a) (y b)))
          | replace (y' b) with (fy (y' a) (finvy (y' a) (y' b)))]; auto;
            apply mono_opp...
      exists (fy (y' b) (-t)).
      subst in_y.
      split.
        split.
          replace (y a) with (fy (y' b) (finvy (y' b) (y a)))...
          apply mono_opp.
          rewrite (inv_inv fym fyf finvy finvy_correct (y' b) (y a))...
        replace (y' a) with (fy (y' b) (finvy (y' b) (y' a)))...
        apply mono_opp.
        rewrite (inv_inv fym fyf finvy finvy_correct (y' b) (y' a))...
      rewrite <- (concrete.flow_additive fyf)...
      replace (- t + t) with 0...
      rewrite (concrete.flow_zero fyf)...
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
        destruct (inv_nonneg fxm fxf finvx finvx_correct (x a) (x' b)).
        apply H16.
        apply mle_trans with (x' a)...
      destruct (inv_nonneg fym fyf finvy finvy_correct (y a) (y' b)).
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
