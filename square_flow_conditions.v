Require Import util.
Require Import c_util.
Require Import monotonic_flow.
Require Import geometry.
Set Implicit Arguments.
Open Local Scope CR_scope.

Section omle.

  Variables (f: Flow CRasCSetoid) (fm: mono f).

  Definition omle (x y: option CR): Prop :=
    if fm then OCRle x y else OCRle y x.

  Definition omle_dec (e: Qpos) (x y: option CR): bool :=
    if fm then overestimate_OCRle e x y else overestimate_OCRle e y x.

End omle.

Module one_axis.
Section contents.

  Variables
     (f: Flow CRasCSetoid)
     (finv: CR -> CR -> Time)
     (finv_correct: forall x x', f x (finv x x') == x')
     (fm: mono f)
     (oa ob: OpenRange).

  Let ox: OpenRange -> option CR := if fm then orange_left else orange_right.
  Let ox': OpenRange -> option CR := if fm then orange_right else orange_left.

  Definition in_or (r: OpenRange) (ux: CR): Prop :=
    omle fm (ox r) (Some ux) /\ omle fm (Some ux) (ox' r).

  Definition in_orange_alt r p: in_orange p r <-> in_or p r.
    unfold in_orange, in_or, ox, ox', orange_left, orange_right.
    destruct p.
    destruct x.
    unfold omle.
    simpl.
    destruct s; destruct s0; destruct fm; tauto.
  Qed.

  Definition low: option Time :=
      flip_opt None (ox' oa) (fun x'a => flip_opt None (ox ob) (fun xb =>
        Some (finv x'a xb))).
  Definition high: option Time :=
      flip_opt None (ox oa) (fun xa => flip_opt None (ox' ob) (fun x'b =>
        Some (finv xa x'b))).

  Lemma low_le_high: uncurry OCRle (low, high).
  Proof with simpl; auto.
    unfold uncurry, OCRle, low, high.
    destruct oa. destruct ob. unfold ox, ox', fst.
    set (inv_le_left fm finv finv_correct).
    set (inv_le fm finv finv_correct).
    unfold orange_left, orange_right.
    destruct x. destruct x0.
    destruct fm.
      destruct s0...  destruct s1... destruct s... destruct s2...
      apply CRle_trans with (finv s0 s2)...
    destruct s... destruct s2... destruct s0... destruct s1...
    apply CRle_trans with (finv s s1)...
  Qed.

  Definition flow_range: OpenRange := existT _ _ low_le_high.

  Lemma flow_range_covers p:
    in_orange oa p -> forall t, in_orange ob (f p t) -> in_orange flow_range t.
  Proof with auto.
    intros.
    unfold flow_range.
    unfold in_orange, orange_left, orange_right in *.
    simpl.
    unfold low, high.
    destruct H. destruct H0.
    subst ox ox'.
    destruct oa. destruct ob.
    unfold orange_left, orange_right in *.
    set (inv_le fm finv finv_correct).
    set (inv_le_left fm finv finv_correct).
    destruct x. destruct x0.
    simpl proj1_sig in *. simpl @fst in *. simpl @snd in *.
    unfold opt_prop, util.flip.
    split.
      destruct fm; simpl proj1_sig.
        destruct s0... destruct s1...
        simpl.
        rewrite <- (inv_correct' fm finv finv_correct p t).
        apply CRle_trans with (finv s0 (f p t))...
      destruct s... destruct s2...
      simpl.
      rewrite <- (inv_correct' fm finv finv_correct p t).
      apply CRle_trans with (finv s (f p t))...
    destruct fm; simpl proj1_sig.
      destruct s... destruct s2...
      simpl.
      rewrite <- (inv_correct' fm finv finv_correct p t).
      apply CRle_trans with (finv s (f p t))...
    destruct s0... destruct s1...
    simpl.
    rewrite <- (inv_correct' fm finv finv_correct p t).
    apply CRle_trans with (finv s0 (f p t))...
  Qed.

End contents.
End one_axis.

Hint Resolve one_axis.flow_range_covers.

Section contents.

  Variables
     (fx fy: Flow CRasCSetoid)
     (finvx finvy: OpenRange -> OpenRange -> OpenRange) (* last range is a duration range *)
     (oa ob: OpenSquare).

  Definition f (p: Point) (t: Time): Point := (fx (fst p) t, fy (snd p) t).

  Definition ideal: Prop :=
    exists p: Point, in_osquare p oa /\
    exists t: Time, 0 <= t /\ in_osquare (f p t) ob.

  Definition naive_ideal: Prop :=
    exists p: Point, in_osquare p oa /\
    exists t: Time, in_osquare (f p t) ob.
    (* naive because it doesn't require 0<=t *)

  Definition xflow_range: OpenRange := finvx (fst oa) (fst ob).
  Definition yflow_range: OpenRange := finvy (snd oa) (snd ob).

  Definition naive_decideable: Prop :=
    oranges_overlap xflow_range yflow_range.

  Definition practical_decideable: Prop :=
    naive_decideable /\
    opt_prop (CRmin_of_upper_bounds (snd (`xflow_range)) (snd (`yflow_range))) CRnonNeg.

  Definition decide_practical eps: overestimation practical_decideable :=
    overestimate_conj
      (overestimate_oranges_overlap eps xflow_range yflow_range)
      (opt_overestimation (CRnonNeg) (overestimate_CRnonNeg eps)
        (CRmin_of_upper_bounds (snd (`xflow_range)) (snd (`yflow_range)))).

  Variables
     (finvx_correct: 
       forall r x, in_orange r x -> forall t u, in_orange u (fx x t) -> in_orange (finvx r u) t)
     (finvy_correct: 
       forall r y, in_orange r y -> forall t u, in_orange u (fy y t) -> in_orange (finvy r u) t).

  Lemma naive_ideal_decideable: naive_ideal -> naive_decideable.
  Proof with auto.
    unfold naive_ideal, naive_decideable.
    intros [[x y] [[ia b] [t [c d]]]].
    unfold xflow_range, yflow_range.
    apply oranges_share_point with t; eauto.
  Qed.

  Lemma ideal_implies_practical_decideable: ideal -> practical_decideable.
  Proof with auto.
    intros [[x y] [[i i'] [t [tle [j j']]]]].
    split.
      unfold naive_decideable.
      apply naive_ideal_decideable.
      unfold naive_ideal.
      exists (x, y). split. split... exists t... split...
    unfold xflow_range, yflow_range.
    set (finvx_correct i t j).
    set (finvy_correct i' t j').
    clearbody i0 i1.
    unfold CRmin_of_upper_bounds.
    destruct (finvx (fst oa) (fst ob)).
    destruct (finvy (snd oa) (snd ob)).
    simpl proj1_sig.
    destruct x0. destruct x1.
    unfold in_orange in *. unfold orange_left, orange_right in *.
    simpl proj1_sig in *.
    destruct i1. destruct i0.
    simpl @fst in *. simpl @snd in *.
    destruct s0; destruct s2; auto; apply <- CRnonNeg_le_zero; apply CRle_trans with t...
    apply CRmin_glb...
  Qed.

End contents.

