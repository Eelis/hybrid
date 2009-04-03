Require Import util.
Require Import c_util.
Require Import c_monotonic_flow.
Require Import c_geometry.
Set Implicit Arguments.
Open Local Scope CR_scope.

Definition OCRle_dec (e: Qpos) (o: option CR * option CR): bool :=
  match o with
  | (Some p, Some q) => CRnonNeg_dec e (q - p)
  | _ => true
  end.

Definition over_OCRle eps: @OCRle_dec eps >=> OCRle.
  repeat intro.
  destruct a.
  destruct o; try discriminate.
  destruct o0; try discriminate.
  apply (over_CRnonNeg eps H).
  assumption.
Qed.

Section omle.

  Variables (f: Flow CRasCSetoid) (fm: mono f).

  Definition omle (x y: option CR): Prop :=
    if fm then OCRle (x, y) else OCRle (y, x).

  Definition omle_dec (e: Qpos) (x y: option CR): bool :=
    if fm then OCRle_dec e (x, y) else OCRle_dec e (y, x).

  Lemma over_omle eps p: omle_dec eps p >=> omle p.
  Proof.
    unfold omle_dec, omle. repeat intro.
    destruct fm; apply (over_OCRle eps _ H); assumption.
  Qed.

End omle.

Module one_axis.
Section contents.

  Variables
     (f: Flow CRasCSetoid)
     (finv: CR -> CR -> Time)
     (finv_correct: forall x x', f x (finv x x') == x')
     (fm: mono f)  (a b: Range).
  Variables (oa ob: OpenRange).

  Let x: Range -> CR := if fm then range_left else range_right.
  Let x': Range -> CR := if fm then range_right else range_left.

  Let ox: OpenRange -> option CR := if fm then orange_left else orange_right.
  Let ox': OpenRange -> option CR := if fm then orange_right else orange_left.

  Definition in_r (r: Range) ux: Prop := mle fm (x r) ux /\ mle fm ux (x' r).

  Definition in_or (r: OpenRange) (ux: CR): Prop :=
    omle fm (ox r) (Some ux) /\ omle fm (Some ux) (ox' r).

  Definition in_range_alt r p: in_range p r <-> in_r p r.
    unfold in_range, in_r, x, x'.
    destruct p. unfold range_left, range_right.
    simpl.
    destruct fm; tauto.
  Qed.

  Definition in_orange_alt r p: in_orange p r <-> in_or p r.
    unfold in_orange, in_or, ox, ox', orange_left, orange_right, x, x'.
    destruct p.
    destruct x0.
    unfold omle.
    simpl.
    destruct o0; destruct o1; destruct fm; tauto.
  Qed.

  Add Morphism (@bsm CRasCSetoid CRasCSetoid CRasCSetoid)
    with signature (@eq _) ==> (@cs_eq _) ==> (@cs_eq _) ==> (@cs_eq _)
    as gh_mor.
  Proof. intro. exact (@bsm_mor _ _ _ y y (refl_equal _)). Qed.

  Add Morphism finv with signature (@cs_eq _) ==> (@cs_eq _) ==> (@cs_eq _)
    as finv_wd.
  Proof. intros. apply (inv_wd fm); assumption. Qed.

  Lemma dammit (x: CR): x == x.
    reflexivity.
  Qed.

  Hint Immediate dammit.

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
  Variables (oa ob: OpenSquare).

  Definition f (p: Point) (t: Time): Point := (fx (fst p) t, fy (snd p) t).

  Let x  (s: Square): CR := (if fxm then range_left  else range_right) (fst s).
  Let x' (s: Square): CR := (if fxm then range_right else range_left ) (fst s).
  Let y  (s: Square): CR := (if fym then range_left  else range_right) (snd s).
  Let y' (s: Square): CR := (if fym then range_right else range_left ) (snd s).

  Let ox  (s: OpenSquare): option CR := (if fxm then orange_left  else orange_right) (fst s).
  Let ox' (s: OpenSquare): option CR := (if fxm then orange_right else orange_left ) (fst s).
  Let oy  (s: OpenSquare): option CR := (if fym then orange_left  else orange_right) (snd s).
  Let oy' (s: OpenSquare): option CR := (if fym then orange_right else orange_left ) (snd s).

  Let in_x (s: Square) ux: Prop := mle fxm (x s) ux /\ mle fxm ux (x' s).
  Let in_y (s: Square) uy: Prop := mle fym (y s) uy /\ mle fym uy (y' s).

  Let in_ox (s: OpenSquare) (ux: CR): Prop := omle fxm (ox s) (Some ux) /\ omle fxm (Some ux) (ox' s).
  Let in_oy (s: OpenSquare) (uy: CR): Prop := omle fym (oy s) (Some uy) /\ omle fym (Some uy) (oy' s).

  Let mle_x_x' s: mle fxm (x s) (x' s).
  Proof. intros [[[c i] d] [[u p] v]]. destruct fxm; auto. Qed.

  Let omle_x_x' s: omle fxm (ox s) (ox' s).
  Proof. intros [[[c i] d] [[u p] v]]. destruct fxm; auto. Qed.

  Let omle_y_y' s: omle fym (oy s) (oy' s).
  Proof. intros [[[c i] d] [[u p] v]]. destruct fym; auto. Qed.

  Let mle_y_y' s: mle fym (y s) (y' s).
  Proof. intros [[[c i] d] [[u p] v]]. destruct fym; auto. Qed.

  Hint Immediate mle_x_x' mle_y_y'.

  Let in_s s (p: Point): Prop :=
    in_x s (fst p) /\ in_y s (snd p).
    (* expressed in terms of the mono accessors, makes reasoning easier *)

  Let in_os (s: OpenSquare) (p: Point): Prop :=
    in_ox s (fst p) /\ in_oy s (snd p).

  Definition in_square_alt s p: in_square p s <-> in_s s p.
    unfold in_square, in_s, in_x, in_y.
    destruct s. destruct p. destruct r. destruct r0.
    subst x x' y y'.
    simpl. unfold in_range.
    destruct fxm; destruct fym; tauto.
  Qed.

  Definition in_osquare_alt s p: in_osquare p s <-> in_os s p.
    unfold in_osquare, in_os, in_ox, in_oy.
    intros [[c u] [d v]] [px py].
    subst ox ox' oy oy'.
    simpl. unfold in_orange.
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

  Definition oideal: Prop :=
    exists p: Point, in_osquare p oa /\
    exists t: Time, '0 <= t /\ in_osquare (f p t) ob.

  Definition naive_ideal: Prop :=
    exists p: Point, in_square p a /\
    exists t: Time, in_square (f p t) b.
    (* naive because it doesn't require 0<=t *)

  Definition onaive_ideal: Prop :=
    exists p: Point, in_osquare p oa /\
    exists t: Time, in_osquare (f p t) ob.
    (* naive because it doesn't require 0<=t *)

  Definition naive_decideable: Prop :=
    finvx (x' a) (x b) <= finvy (y a) (y' b) /\
    finvy (y' a) (y b) <= finvx (x a) (x' b).
    (* naive in the same way *)

  Definition opt_prop A (o: option A) (f: A -> Prop): Prop :=
    match o with
    | None => True
    | Some v => f v
    end.

  Definition onaive_decideable: Prop :=
    opt_prop (ox' oa) (fun x'a =>
    opt_prop (ox ob) (fun xb =>
    opt_prop (oy oa) (fun ya =>
    opt_prop (oy' ob) (fun y'b =>
      finvx x'a xb <= finvy ya y'b
    )))) /\
    opt_prop (oy' oa) (fun y'a =>
    opt_prop (oy ob) (fun yb =>
    opt_prop (ox oa) (fun xa =>
    opt_prop (ox' ob) (fun x'b =>
      finvy y'a yb <= finvx xa x'b
    )))).

  Definition opt {A R}: (A -> R) -> R -> option A -> R :=
    option_rect (fun _ => R).

  Definition flip_opt {A R} (r: R) (o: option A) (f: A -> R): R :=
    option_rect (fun _ => R) f r o.

  Definition onaive_dec eps (_: unit): bool :=
    flip_opt true (ox' oa) (fun x'a =>
    flip_opt true (ox ob) (fun xb =>
    flip_opt true (oy oa) (fun ya =>
    flip_opt true (oy' ob) (fun y'b =>
      CRle_dec eps (finvx x'a xb, finvy ya y'b)
    )))) &&
    flip_opt true (oy' oa) (fun y'a =>
    flip_opt true (oy ob) (fun yb =>
    flip_opt true (ox oa) (fun xa =>
    flip_opt true (ox' ob) (fun x'b =>
      CRle_dec eps (finvy y'a yb, finvx xa x'b)
    )))).
  
  (* While these naive conditions aren't suitable for actual use,
   they are neatly equivalent. *)

  Lemma inv_nonneg_snd_x x x': mle fxm x x' -> '0 <= finvx x x'.
    intros. apply <- inv_nonneg; eauto.
  Qed.

  Lemma inv_nonneg_snd_y y y': mle fym y y' -> '0 <= finvy y y'.
    intros. apply <- inv_nonneg; eauto.
  Qed.

  Hint Resolve inv_nonneg_snd_x.
  Hint Resolve inv_nonneg_snd_y.
  Hint Immediate CRle_refl.
  Hint Resolve t9.

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
    split; apply CRle_trans with t.
          rewrite <- (inv_correct' fxm finvx finvx_correct ux t).
          rewrite (inv_plus fxm finvx finvx_correct ux (x' a) (fx ux t)).
          rewrite (inv_plus fxm finvx finvx_correct (x' a) (x b) (fx ux t)).
          rewrite <- (Radd_0_l CR_ring_theory (finvx (x' a) (x b))) at 1.
          apply t9...
          rewrite <- (Radd_0_l CR_ring_theory (finvx (x' a) (x b))) at 1.
          rewrite (Radd_comm CR_ring_theory)...
        rewrite <- (inv_correct' fym finvy finvy_correct uy t).
        rewrite (inv_plus fym finvy finvy_correct (y a) uy (y' b)).
        rewrite (inv_plus fym finvy finvy_correct uy (fy uy t) (y' b)).
        rewrite <- (Radd_0_l CR_ring_theory (finvy uy (fy uy t))) at 1.
        apply t9...
        rewrite <- (Radd_0_l CR_ring_theory (finvy uy (fy uy t))) at 1.
        rewrite (Radd_comm CR_ring_theory)...
      rewrite <- (inv_correct' fym finvy finvy_correct uy t).
      rewrite (inv_plus fym finvy finvy_correct uy (y' a) (fy uy t)).
      rewrite (inv_plus fym finvy finvy_correct (y' a) (y b) (fy uy t)).
      rewrite <- (Radd_0_l CR_ring_theory (finvy (y' a) (y b))) at 1.
      apply t9...
      rewrite <- (Radd_0_l CR_ring_theory (finvy (y' a) (y b))) at 1.
      rewrite (Radd_comm CR_ring_theory)...
    rewrite <- (inv_correct' fxm finvx finvx_correct ux t).
    rewrite (inv_plus fxm finvx finvx_correct (x a) ux (x' b)).
    rewrite (inv_plus fxm finvx finvx_correct ux (fx ux t) (x' b)).
    rewrite <- (Radd_0_l CR_ring_theory (finvx ux (fx ux t))) at 1.
    apply t9...
    rewrite <- (Radd_0_l CR_ring_theory (finvx ux (fx ux t))) at 1.
    rewrite (Radd_comm CR_ring_theory)...
  Qed.

  Lemma onaive_ideal_implies_onaive_decideable: onaive_ideal -> onaive_decideable.
  Proof with auto.
    unfold onaive_ideal, onaive_decideable.
    intros [p [io [t iof]]]. intros.
    set (io' := fst (in_osquare_alt oa p) io).
      clearbody io'. clear io.
    set (iof' := fst (in_osquare_alt ob (f p t)) iof).
      clearbody iof'. clear iof.
    destruct io'. destruct iof'.
    destruct p as [ux uy].
    destruct H. destruct H0. destruct H1. destruct H2.
    split.
      case_eq (ox' oa); intros; simpl...
      case_eq (ox ob); intros; simpl...
      case_eq (oy oa); intros; simpl...
      case_eq (oy' ob); intros; simpl...
      rewrite H10 in H6. rewrite H9 in H0.
      rewrite H7 in H3. rewrite H8 in H1.
      apply CRle_trans with t.
        rewrite <- (inv_correct' fxm finvx finvx_correct ux t).
        rewrite (inv_plus fxm finvx finvx_correct ux m (fx ux t)).
        rewrite (inv_plus fxm finvx finvx_correct m m0 (fx ux t)).
        rewrite <- (Radd_0_l CR_ring_theory (finvx m m0)) at 1.
        apply t9...
        rewrite <- (Radd_0_l CR_ring_theory (finvx m m0)) at 1.
        rewrite (Radd_comm CR_ring_theory)...
      rewrite <- (inv_correct' fym finvy finvy_correct uy t).
      rewrite (inv_plus fym finvy finvy_correct m1 uy m2).
      rewrite (inv_plus fym finvy finvy_correct uy (fy uy t) m2).
      rewrite <- (Radd_0_l CR_ring_theory (finvy uy (fy uy t))) at 1.
      apply t9...
      rewrite <- (Radd_0_l CR_ring_theory (finvy uy (fy uy t))) at 1.
      rewrite (Radd_comm CR_ring_theory)...
    case_eq (oy' oa); intros; simpl...
    case_eq (oy ob); intros; simpl...
    case_eq (ox oa); intros; simpl...
    case_eq (ox' ob); intros; simpl...
    rewrite H7 in H4. rewrite H8 in H2.
    rewrite H9 in H. rewrite H10 in H5.
    apply CRle_trans with t.
      rewrite <- (inv_correct' fym finvy finvy_correct uy t).
      rewrite (inv_plus fym finvy finvy_correct uy m (fy uy t)).
      rewrite (inv_plus fym finvy finvy_correct m m0 (fy uy t)).
      rewrite <- (Radd_0_l CR_ring_theory (finvy m m0)) at 1.
      apply t9...
      rewrite <- (Radd_0_l CR_ring_theory (finvy m m0)) at 1.
      rewrite (Radd_comm CR_ring_theory).
      apply t9...
    rewrite <- (inv_correct' fxm finvx finvx_correct ux t).
    rewrite (inv_plus fxm finvx finvx_correct m1 ux m2).
    rewrite (inv_plus fxm finvx finvx_correct ux (fx ux t) m2).
    rewrite <- (Radd_0_l CR_ring_theory (finvx ux (fx ux t))) at 1.
    apply t9...
    rewrite <- (Radd_0_l CR_ring_theory (finvx ux (fx ux t))) at 1.
    rewrite (Radd_comm CR_ring_theory)...
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

  Definition opractical_decideable: Prop :=
    onaive_decideable /\
    omle fxm (ox oa) (ox' ob) /\ omle fym (oy oa) (oy' ob).

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

Lemma omle_trans f (m: mono f) (x: option CR) (y: CR):
  omle m x (Some y) -> forall z, omle m (Some y) z -> omle m x z.
Proof with auto.
  intros.
  unfold omle in *.
  destruct m.
    destruct x0; destruct z...
    apply CRle_trans with m0...
    apply CRle_trans with y0...
  destruct x0; destruct z...
  apply CRle_trans with m0...
  apply CRle_trans with y0...
Qed.  

  Lemma oideal_implies_opractical_decideable:
    oideal -> opractical_decideable.
  Proof with eauto.
    unfold oideal, opractical_decideable.
    intros [c [d [g [j e]]]].
    split.
      apply onaive_ideal_implies_onaive_decideable.
      unfold onaive_ideal...
    set (fst (in_osquare_alt oa c) d). clearbody i. clear d.
    set (fst (in_osquare_alt ob (f c g)) e). clearbody i0. clear e.
    destruct c. rename g into t. rename c into ux. rename c0 into uy.
    destruct i. destruct i0. simpl in *.
    destruct H. destruct H0. destruct H1. destruct H2.
    split.
      apply omle_trans with ux...
      apply omle_trans with (fx ux t)...
      apply mle_flow...
    apply omle_trans with uy...
    apply omle_trans with (fy uy t)...
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

  Lemma over_onaive_dec eps: onaive_dec eps >=> fun _ => onaive_decideable.
  Proof with auto.
    intros eps q n_d [o1 o2]. unfold onaive_dec in n_d.
    destruct (andb_false_elim _ _ n_d); clear n_d.
      destruct (ox' oa); try discriminate.
      destruct (ox ob); try discriminate.
      destruct (oy oa); try discriminate.
      destruct (oy' ob); try discriminate.
      apply (over_CRnonNeg eps e)...
    destruct (oy' oa); try discriminate.
    destruct (oy ob); try discriminate.
    destruct (ox oa); try discriminate.
    destruct (ox' ob); try discriminate.
    apply (over_CRnonNeg eps e)...
  Qed.

  Definition practical_dec eps (_ : unit) : bool :=
    naive_dec eps () && 
    (if fxm then CRle_dec eps (x a, x' b) else CRle_dec eps (x' b, x a)) &&
    (if fym then CRle_dec eps (y a, y' b) else CRle_dec eps (y' b, y a)).

  Definition opractical_dec eps (_ : unit) : bool :=
    onaive_dec eps () &&
    omle_dec fxm eps (ox oa) (ox' ob) &&
    omle_dec fym eps (oy oa) (oy' ob).

  Lemma over_practical_dec eps : 
    practical_dec eps >=> fun _ => practical_decideable.
  Proof with auto.
    intros eps q n_d [nd [o1 o2]]. unfold practical_dec in n_d.
    band_discr. bool_solver.
    apply (over_true () (over_naive_dec eps))...
    generalize o1. case fxm; intros; estim (over_CRle eps).
    generalize o2. case fym; intros; estim (over_CRle eps).
  Qed.

  Lemma over_opractical_dec eps : 
    opractical_dec eps >=> fun _ => opractical_decideable.
  Proof with auto.
    intros eps q n_d [nd [o1 o2]]. unfold opractical_dec in n_d.
    destruct (andb_false_elim _ _ n_d).
      destruct (andb_false_elim _ _ e).
        apply (over_onaive_dec _ e0)...
      apply (over_omle _ _ _ _ e0)...
    apply (over_omle _ _ _ _ e)...
  Qed.

End contents.
