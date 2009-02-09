Require Import util.
Require Import Fourier.
Require concrete.
Set Implicit Arguments.
Open Local Scope R_scope.

Require Import Coq.Reals.Reals.

Section function_properties.

  Variable f: R -> R.

  Definition strongly_increasing: Prop :=
    forall x x', x < x' -> f x < f x'.
  Definition strongly_decreasing: Prop :=
    forall x x', x < x' -> f x' < f x.

  Definition monotonic: Set := { strongly_increasing } + { strongly_decreasing }.

  Lemma mono_eq: monotonic -> forall x x', f x = f x' <-> x = x'.
  Proof with auto.
    split.
      intros.
      destruct (Rle_lt_dec x x').
        destruct r...
        elimtype False.
        destruct H; set (s _ _ H1); rewrite H0 in r; apply Rlt_irrefl with (f x')...
      elimtype False.
      destruct H; set (s _ _ r); rewrite H0 in r0; apply Rlt_irrefl with (f x')...
    intros. subst...
  Qed.

End function_properties.

Section single_inverses.

  Variable f: R -> Time -> R.

  Definition mono: Set :=
    { forall x, strongly_increasing (f x) } +
    { forall x, strongly_decreasing (f x) }.

  Variable fmono: mono.

  Lemma purify_mono: forall x, monotonic (f x).
  Proof.
    intros.
    unfold monotonic.
    destruct fmono; set (s x); [left | right]; assumption.
  Qed.

  Definition mle (x x': R): Prop := if fmono then x <= x' else x' <= x.
  Definition mlt (x x': R): Prop := if fmono then x < x' else x' < x.

  Lemma mle_refl x: mle x x.
  Proof. unfold mle. destruct fmono; simpl; auto with real. Qed.

  Lemma mle_trans x y z: mle x y -> mle y z -> mle x z.
  Proof.
    unfold mle.
    destruct fmono; simpl; intros; apply Rle_trans with y; assumption.
  Qed.

  Lemma mlt_le x x': mlt x x' -> mle x x'.
  Proof. unfold mlt, mle. destruct fmono; simpl; auto with real. Qed.

  Lemma mle_lt_or_eq_dec x x':
    mle x x' -> { mlt x x' } + { x = x' }.
  Proof with auto with real.
    unfold mle, mlt.
    destruct fmono; simpl; intros.
      apply Rle_lt_or_eq_dec...
    destruct (Rle_lt_or_eq_dec _ _ H)...
  Qed.

  Lemma mono_opp v t t': t' <= t -> mle (f v t') (f v t).
  Proof with auto with real.
    unfold mle.
    destruct fmono.
      intros.
      set (s v).
      unfold strongly_increasing in s0.
      destruct H...
      subst...
    intros.
    set (s v).
    unfold strongly_increasing in s0.
    destruct H...
    subst...
  Qed.

  Variables
    (f_flows: concrete.flows f)
    (inv: R -> R -> Time)
    (inv_correct: forall x x', f x (inv x x') = x').

  Definition f_eq x t t': f x t = f x t' <-> t = t'
    := mono_eq (purify_mono x) t t'.

  Lemma inv_correct' x t: inv x (f x t) = t.
  Proof.
    intros.
    destruct (f_eq x (inv x (f x t)) t).
    clear H0. apply H.
    rewrite inv_correct. reflexivity.
  Qed.

  Hint Immediate f_flows.

  Lemma inv_plus x y z: inv x z = inv x y + inv y z.
  Proof with auto.
    intros. destruct (f_eq x (inv x z) (inv x y + inv y z)).
    clear H0. apply H.
    rewrite concrete.flow_additive...
    repeat rewrite inv_correct...
  Qed.

  Lemma inv_refl x: inv x x = 0.
  Proof with auto.
    intros. destruct (f_eq x (inv x x) 0).
    clear H0. apply H.
    repeat rewrite inv_correct...
    rewrite concrete.flow_zero...
  Qed.

  Lemma f_lt x t t': mlt (f x t) (f x t') -> t < t'.
  Proof with auto with real.
    unfold mlt.
    destruct fmono.
      intros.
      destruct (Rle_lt_dec t t').
        destruct r...
        subst.
        elimtype False.
        apply Rlt_irrefl with (f x t')...
      elimtype False.
      apply (Rlt_asym (f x t') (f x t))...
      apply s...
    intros.
    destruct (Rle_lt_dec t t').
      destruct r...
      subst.
      elimtype False.
      apply Rlt_irrefl with (f x t')...
    elimtype False.
    apply (Rlt_asym (f x t) (f x t'))...
    apply s...
  Qed.

  Lemma f_le x t t': mle (f x t) (f x t') -> t <= t'.
  Proof with auto with real.
    unfold mle.
    intros.
    set (f_lt x t t'). clearbody r.
    unfold mlt in r.
    destruct fmono; destruct H.
          apply Rlt_le...
        right. destruct (f_eq x t t')...
      apply Rlt_le...
    right. destruct (f_eq x t t')...
  Qed.

  Lemma inv_lt_right a x x': inv a x < inv a x' <-> mlt x x'.
  Proof with auto.
    unfold mlt.
    split; intros.
      replace x with (f a (inv a x))...
      replace x' with (f a (inv a x'))...
      destruct fmono; apply s...
    set f_lt. clearbody r.
    unfold mlt in r.
    destruct fmono; apply r with a; repeat rewrite inv_correct...
  Qed.

  Lemma inv_pos x x': 0 < inv x x' <-> mlt x x'.
  Proof with auto with real.
    unfold mlt.
    split; intros.
      set f_lt. clearbody r.
      intros.
      destruct f_flows...
      replace x with (f x 0)...
      replace x' with (f x (inv x x'))...
      destruct fmono; apply s...
    rewrite <- inv_refl with x.
    destruct (inv_lt_right x x x')...
  Qed.

  Lemma inv_very_correct t x: inv (f x t) x = -t.
  Proof with auto with real.
    intros.
    assert (inv x x = 0).
      apply inv_refl.
    rewrite (inv_plus x (f x t) x) in H.
    rewrite inv_correct' in H.
    replace (-t) with (0-t)...
    rewrite <- H.
    unfold Rminus.
    rewrite Rplus_comm.
    rewrite <- Rplus_assoc.
    rewrite Rplus_opp_l...
  Qed.

  Lemma inv_inv x y: inv x y = - inv y x.
  Proof with auto with real.
    intros.
    set (inv_very_correct (inv y x) y).
    rewrite inv_correct in e...
  Qed.

  Lemma inv_uniq_0 x x': inv x x' = - inv 0 x + inv 0 x'.
  Proof.
    intros.
    rewrite (inv_plus x 0 x').
    rewrite (inv_inv x 0).
    auto with real.
  Qed.
    (* hm, this shows that inv is uniquely determined by the values it
      takes with 0 as first argument. perhaps the reason we don't
      just take inv as a unary function is that it is problematic
      for flow functions with singularities at 0? *)

  Lemma inv_le a x x': mle x x' -> inv a x <= inv a x'.
  Proof with auto.
    intros.
    set f_le. clearbody r.
    apply r with a.
    do 2 rewrite inv_correct...
  Qed.

  Lemma inv_nonneg x x': 0 <= inv x x' <-> mle x x'.
  Proof with auto with real.
    unfold mle.
    destruct f_flows.
    split; intros.
      set f_le. clearbody r.
      intros.
      destruct f_flows.
      replace x with (f x 0)...
      replace x' with (f x (inv x x'))...
      apply mono_opp...
    rewrite <- inv_refl with x.
    apply inv_le...
  Qed.

  Lemma inv_zero x x': inv x x' = 0 <-> x = x'.
  Proof with auto.
    split; intros.
      replace x' with (f x (inv x x'))...
      rewrite H.
      rewrite concrete.flow_zero...
    subst.
    rewrite inv_refl...
  Qed.

  Lemma f_lt_left x x' t: x < x' <-> f x t < f x' t.
  Proof with auto with real.
    split.
      intros.
      replace x' with (f x (inv x x'))...
      rewrite <- concrete.flow_additive...
      destruct (inv_pos x x').
      destruct (inv_pos x' x).
      unfold mlt in *.
      destruct fmono.
        apply s.
        set (H1 H).
        fourier.
      apply s.
      rewrite inv_inv.
      set (H3 H).
      fourier.
    set f_lt. set inv_pos. clearbody r i.
    destruct f_flows.
    unfold mlt in r, i.
    destruct fmono; intros.
      replace (f x' t) with (f (f x (inv x x')) t) in H...
        rewrite <- concrete.flow_additive in H...
        set (r _ _ _ H).
        assert (0 < inv x x') by fourier.
        destruct (i x x').
        apply H1...
      rewrite inv_correct...
    replace (f x t) with (f (f x' (inv x' x)) t) in H...
      rewrite <- (concrete.flow_additive f_flows) in H...
      set (r _ _ _ H).
      assert (0 < inv x' x) by fourier.
      destruct (i x' x).
      apply H1...
    destruct f_flows...
    rewrite inv_correct...
  Qed.

  Lemma f_eq_left x x' t: f x t = f x' t <-> x = x'.
  Proof with auto with real.
    intros.
    split; intros.
      intros.
      destruct (Rlt_le_dec x x').
        elimtype False.
        destruct (f_lt_left x x' t).
        set (H0 r).
        rewrite H in r0.
        apply (Rlt_asym _ _ r0)...
      destruct (Rle_lt_or_eq_dec _ _ r)...
      elimtype False.
      destruct (f_lt_left x' x t).
      set (H0 r0).
      rewrite H in r1.
      apply (Rlt_asym _ _ r1)...
    subst...
  Qed.

  Lemma f_le_left x x' t: x <= x' <-> f x t <= f x' t.
  Proof with auto with real.
    intros.
    destruct (f_lt_left x x' t).
    split; intro.
      destruct H1...
      subst...
    destruct H1.
      destruct (f_lt_left x x' t)...
    replace x' with x...
    destruct (f_eq_left x x' t)...
  Qed.

  Lemma inv_lt_left a x x': mlt x x' <-> inv x' a < inv x a.
  Proof with auto with real.
    unfold mlt.
    intros.
    rewrite (inv_inv x' a).
    rewrite (inv_inv x a).
    destruct (inv_lt_right a x x').
    split...
    intros.
    apply H...
  Qed.

  Lemma inv_le_left a x x': mle x x' -> inv x' a <= inv x a.
  Proof with auto with real.
    unfold mle. intros.
    destruct (inv_lt_left a x x').
    unfold mlt in *.
    destruct fmono; intros; destruct H; subst...
  Qed.

  Lemma inv_eq_right a x x': inv a x = inv a x' <-> x = x'.
  Proof with auto with real.
    split.
      intros.
      replace x with (f a (inv a x))...
      replace x' with (f a (inv a x'))...
    intros...
  Qed.

  Lemma inv_le_right a x x': inv a x <= inv a x' <-> mle x x'.
  Proof with auto with real.
    intros.
    destruct (inv_lt_right a x x').
    split; intro.
      destruct H1.
        apply mlt_le...
      rewrite (conj_fst (inv_eq_right a x x') H1).
      apply mle_refl.
    destruct (mle_lt_or_eq_dec _ _ H1)...
    subst...
  Qed.

  Lemma mle_flow t x: 0 <= t -> mle x (f x t).
  Proof with auto.
    intros.
    apply mle_trans with (f x 0).
      rewrite concrete.flow_zero...
      apply mle_refl.
    apply mono_opp...
  Qed.

End single_inverses.
