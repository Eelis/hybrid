Require Import util.
Require Import c_util.
Require Export flow.
Set Implicit Arguments.
Open Local Scope CR_scope.

Section single_inverses.

  Variable f: Flow CRasCSetoid.

  Variable fmono: mono f.

  Lemma purify_mono: forall x, monotonic (f x).
  Proof.
    intros.
    unfold monotonic.
    destruct fmono; set (s x); [left | right]; assumption.
  Qed.

  Definition mle (x x': CR): Prop := if fmono then x <= x' else x' <= x.
  Definition mlt (x x': CR): CProp := if fmono then x < x' else x' < x.

  Lemma mle_refl x: mle x x.
  Proof. unfold mle. destruct fmono; intros; apply CRle_refl. Qed.

  Lemma mle_trans x y z: mle x y -> mle y z -> mle x z.
  Proof.
    unfold mle.
    destruct fmono; intros; apply CRle_trans with y; assumption.
  Qed.

  Lemma mlt_le x x': mlt x x' -> mle x x'.
  Proof.
    unfold mlt, mle. destruct fmono; intros; apply CRlt_le; assumption.
  Qed.

  Lemma mono_le_opp v t t': t' < t -> mlt (f v t') (f v t).
  Proof.
    unfold mlt.
    destruct fmono;intros; apply s; assumption.
  Qed.

  Lemma mono_opp v t t': t' <= t -> mle (f v t') (f v t).
  Proof with auto.
    unfold mle.
    destruct fmono; intros.
      apply mildly_increasing...
      intros. rewrite H0. reflexivity.
    apply mildly_decreasing...
    intros. rewrite H0. reflexivity.
  Qed.

  Variables
    (inv: CR -> CR -> Time)
    (inv_correct: forall x x', f x (inv x x') == x').

  Definition f_eq x t t': f x t == f x t' <-> t == t'.
  Proof.
    intros.
    apply mono_eq.
      intros.
      rewrite H.
      reflexivity.
    apply purify_mono.
  Qed.

  Lemma inv_correct' x t: inv x (f x t) == t.
  Proof.
    intros.
    destruct (f_eq x (inv x (f x t)) t).
    clear H0. apply H.
    rewrite inv_correct. reflexivity.
  Qed.

  Add Morphism inv with signature (@cs_eq _) ==> (@cs_eq _) ==> (@cs_eq _)
    as inv_wd.
  Proof with auto.
    intros.
    destruct (f_eq x (inv x x0) (inv y y0)).
    apply H1.
    rewrite inv_correct.
    rewrite H.
    rewrite inv_correct...
  Qed.

  Lemma inv_plus x y z: inv x z == inv x y + inv y z.
  Proof with auto.
    intros. destruct (f_eq x (inv x z) (inv x y + inv y z)).
    clear H0. apply H.
    rewrite flow_additive...
    repeat rewrite inv_correct.
    reflexivity.
  Qed.

  Lemma inv_refl x: inv x x == 0.
  Proof with auto.
    intros. destruct (f_eq x (inv x x) 0).
    clear H0. apply H.
    repeat rewrite inv_correct...
    rewrite flow_zero...
  Qed.

  Lemma f_le x t t': mle (f x t) (f x t') -> t <= t'.
  Proof with auto.
    unfold mle. intros. destruct fmono.
      apply strongly_increasing_inv_mild with (f x)...
    apply strongly_decreasing_inv_mild with (f x)...
  Qed.

  Lemma inv_le_right a x x': inv a x <= inv a x' <-> mle x x'.
  Proof with auto.
    unfold mle.
    split.
      intros.
      destruct fmono.
        rewrite <- (inv_correct a x).
        rewrite <- (inv_correct a x').
        apply mildly_increasing...
        intros. rewrite H0...
      rewrite <- (inv_correct a x).
      rewrite <- (inv_correct a x').
      apply mildly_decreasing...
      intros. rewrite H0...
    set f_le. unfold mle in c. clearbody c.
    intros.
    apply c with a.
    destruct fmono; repeat rewrite inv_correct...
  Qed.

  Lemma inv_very_correct t x: inv (f x t) x == -t.
  Proof with auto with real.
    intros.
    assert (inv x x == 0).
      apply inv_refl.
    rewrite (inv_plus x (f x t) x) in H.
    rewrite inv_correct' in H.
    rewrite <- (Radd_0_l CR_ring_theory (-t)).
    rewrite <- H.
    rewrite (Radd_comm CR_ring_theory).
    rewrite (Radd_assoc CR_ring_theory).
    rewrite (Radd_comm CR_ring_theory (-t)).
    rewrite (Ropp_def CR_ring_theory).
    rewrite (Radd_0_l CR_ring_theory)...
  Qed.

  Lemma inv_inv x y: inv x y == - inv y x.
  Proof with auto.
    intros.
    set (inv_very_correct (inv y x) y).
    clearbody s. rewrite <- s.
    rewrite inv_correct...
  Qed.

  Lemma inv_uniq_0 x x': inv x x' == - inv 0 x + inv 0 x'.
  Proof with auto.
    intros.
    rewrite (inv_plus x 0 x').
    rewrite (inv_inv x 0)...
  Qed.
    (* hm, this shows that inv is uniquely determined by the values it
      takes with 0 as first argument. perhaps the reason we don't
      just take inv as a unary function is that it is problematic
      for flow functions with singularities at 0? *)

  Lemma inv_le a x x': mle x x' -> inv a x <= inv a x'.
  Proof with auto.
    intros.
    set f_le. clearbody c.
    apply c with a.
    unfold mle in *.
    destruct fmono; do 2 rewrite inv_correct...
  Qed.

  Lemma inv_nonneg x x': 0 <= inv x x' <-> mle x x'.
  Proof with auto.
    unfold mle.
    split; intros.
      destruct fmono.
        rewrite <- (flow_zero f x).
        rewrite <- (inv_correct x x').
        apply mildly_increasing...
        intros. rewrite H0...
      rewrite <- (flow_zero f x).
      rewrite <- (inv_correct x x').
      apply mildly_decreasing...
      intros. rewrite H0...
    rewrite <- (inv_refl x).
    apply inv_le...
  Qed.

  Lemma inv_zero x x': inv x x' == 0 <-> x == x'.
  Proof with auto.
    split; intros.
      rewrite <- (inv_correct x x').
      rewrite H, flow_zero...
    rewrite H.
    apply inv_refl.
  Qed.

  Lemma f_le_left x x' t: x <= x' -> f x t <= f x' t.
  Proof with auto with real.
    intros.
    set (inv_nonneg x x').
    set (inv_nonneg x' x).
    clearbody i i0.
    unfold mle in *.
    destruct fmono; clear fmono; destruct f.
      simpl strongly_increasing in s.
      clear f. rename flow_morphism into f.
      rewrite <- (inv_correct x x').
      rewrite <- flow_additive.
      apply mildly_increasing...
        intros. rewrite H0...
      rewrite <- (Radd_0_l CR_ring_theory t) at 1.
      apply t9.
        apply i...
      apply CRle_refl.
    simpl strongly_decreasing in s.
    clear f. rename flow_morphism into f.
    rewrite <- (inv_correct x x').
    simpl.
    rewrite <- flow_additive.
    apply mildly_decreasing...
      intros. rewrite H0...
    rewrite <- (Radd_0_l CR_ring_theory t) at 2.
    apply t9.
      rewrite inv_inv.
      assert (0 == -0).
        rewrite CRopp_Qopp.
        apply inject_Q_CR_wd.
        reflexivity.
      rewrite H0.
      apply t8.
      apply i0...
    apply CRle_refl.
  Qed.

  Lemma inv_le_left a x x': mle x x' -> inv x' a <= inv x a.
  Proof with auto.
    intros.
    rewrite (inv_inv x'). rewrite (inv_inv x).
    apply t8. apply inv_le...
  Qed.

  Lemma mle_flow t x: 0 <= t -> mle x (f x t).
  Proof with auto.
    intros.
    apply mle_trans with (f x 0).
      unfold mle.
      destruct fmono; rewrite flow_zero; apply CRle_refl.
    apply mono_opp...
  Qed.

End single_inverses.

