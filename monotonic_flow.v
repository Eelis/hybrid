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

(*
  Lemma mle_lt_or_eq_dec x x':
    mle x x' -> { mlt x x' } + { x = x' }.
  Proof with auto with real.
    unfold mle, mlt.
    destruct fmono; simpl; intros.
      apply Rle_lt_or_eq_dec...
    destruct (Rle_lt_or_eq_dec _ _ H)...
  Qed.
*)

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

  Lemma inv_refl x: inv x x == '0.
  Proof with auto.
    intros. destruct (f_eq x (inv x x) ('0)).
    clear H0. apply H.
    repeat rewrite inv_correct...
    rewrite flow_zero...
  Qed.

  Lemma f_lt x t t': mlt (f x t) (f x t') -> t < t'.
  Proof with auto.
    unfold mlt. destruct fmono; intros.
      apply strongly_increasing_inv with (f x)...
      intros. rewrite H0...
    apply strongly_decreasing_inv with (f x)...
    intros. rewrite H0...
  Qed.

  Lemma f_le x t t': mle (f x t) (f x t') -> t <= t'.
  Proof with auto.
    unfold mle. intros. destruct fmono.
      apply strongly_increasing_inv_mild with (f x)...
    apply strongly_decreasing_inv_mild with (f x)...
  Qed.

  Lemma inv_lt_right a x x': inv a x < inv a x' IFF mlt x x'.
  Proof with auto.
    unfold mlt.
    split.
      intros.
      destruct fmono.
        assert (x' == x')...
        apply (CRlt_wd (inv_correct a x) H0).
        assert (f a (inv a x) == f a (inv a x))...
        apply (CRlt_wd H1 (inv_correct a x')).
        apply s...
      assert (x' == x')...
      apply (CRlt_wd H0 (inv_correct a x)).
      assert (f a (inv a x) == f a (inv a x))...
      apply (CRlt_wd (inv_correct a x') H1).
      apply s...
    set f_lt. unfold mlt in c. clearbody c.
    destruct fmono.
      intros.
      apply c with a.
      assert (f a (inv a x) == x) by apply inv_correct.
      assert (f a (inv a x') == x') by apply inv_correct.
      symmetry in H0, H1.
      apply (CRlt_wd H0 H1)...
    (* todo: use morphisms to make this much nicer *)
    intros.
    apply c with a.
    assert (f a (inv a x) == x) by apply inv_correct.
    assert (f a (inv a x') == x') by apply inv_correct.
    symmetry in H0, H1.
    apply (CRlt_wd H1 H0)...
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
(*
  Lemma inv_pos x x': '0 < inv x x' IFF mlt x x'.
  Proof with auto with real.
    unfold mlt.
    split; intros.
      admit.
      (*
      set f_lt. clearbody c.
      intros.
      destruct f_flows...
      replace x with (f x ('0))...
      destruct fmono.
        set (inv_correct x x').
        assert (forall h h', h == h' -> f x h == f x h').
          intros.
          apply f_wd...
          reflexivity.
        clearbody m.
        rewrite <- m.
      replace x' with (f x (inv x x'))...
      destruct fmono; apply s...
      *)
    Check (inv_refl).
  Qed.
*)
  Lemma inv_very_correct t x: inv (f x t) x == -t.
  Proof with auto with real.
    intros.
    assert (inv x x == '0).
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

  Lemma inv_uniq_0 x x': inv x x' == - inv ('0) x + inv ('0) x'.
  Proof with auto.
    intros.
    rewrite (inv_plus x ('0) x').
    rewrite (inv_inv x ('0))...
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

  Lemma inv_nonneg x x': '0 <= inv x x' <-> mle x x'.
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

  Lemma inv_zero x x': inv x x' == '0 <-> x == x'.
  Proof with auto.
    split; intros.
      rewrite <- (inv_correct x x').
      rewrite H, flow_zero...
    rewrite H.
    apply inv_refl.
  Qed.

(*
  Lemma f_lt_left x x' t: (x < x') IFF (f x t < f x' t).
  Proof with auto with real.
  Admitted.

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
*)
(*
  Lemma f_eq_left x x' t: f x t == f x' t <-> x == x'.
  Proof with auto with real.
  Admitted.

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
*)

  Lemma f_le_left x x' t: x <= x' -> f x t <= f x' t.
  Proof with auto with real.
    intros.
    set (inv_nonneg x x').
    set (inv_nonneg x' x).
    clearbody i i0.
    unfold mle in *.
    destruct fmono; clear fmono; destruct f.
      simpl strongly_increasing in s.
      simpl. clear f. rename flow_morphism into f.
      rewrite <- (inv_correct x x').
      simpl.
      rewrite <- flow_additive.
      apply mildly_increasing...
        intros. rewrite H0...
      rewrite <- (Radd_0_l CR_ring_theory t) at 1.
      apply t9.
        apply i...
      apply CRle_refl.
    simpl strongly_decreasing in s.
    simpl. clear f. rename flow_morphism into f.
    rewrite <- (inv_correct x x').
    simpl.
    rewrite <- flow_additive.
    apply mildly_decreasing...
      intros. rewrite H0...
    rewrite <- (Radd_0_l CR_ring_theory t) at 2.
    apply t9.
      rewrite inv_inv.
      assert ('0 == -'0).
        rewrite CRopp_Qopp.
        apply inject_Q_wd.
        reflexivity.
      rewrite H0.
      apply t8.
      apply i0...
    apply CRle_refl.
  Qed.

(*
  Lemma inv_lt_left a x x': mlt x x' IFF inv x' a < inv x a.
  Proof with auto with real.
  Admitted.

    unfold mlt.
    intros.
    rewrite (inv_inv x' a).
    rewrite (inv_inv x a).
    destruct (inv_lt_right a x x').
    split...
    intros.
    apply H...
  Qed.
*)
  Lemma inv_le_left a x x': mle x x' -> inv x' a <= inv x a.
  Proof with auto.
    intros.
    rewrite (inv_inv x'). rewrite (inv_inv x).
    apply t8. apply inv_le...
  Qed.

(*
  Lemma inv_eq_right a x x': inv a x = inv a x' <-> x = x'.
  Proof with auto with real.
  Admitted.

    split.
      intros.
      replace x with (f a (inv a x))...
      replace x' with (f a (inv a x'))...
    intros...
  Qed.
*)

  Lemma mle_flow t x: '0 <= t -> mle x (f x t).
  Proof with auto.
    intros.
    apply mle_trans with (f x ('0)).
      unfold mle.
      destruct fmono; rewrite flow_zero; apply CRle_refl.
    apply mono_opp...
  Qed.

End single_inverses.

