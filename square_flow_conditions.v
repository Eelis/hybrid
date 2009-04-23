Require Import util.
Require Import c_util.
Require Import monotonic_flow.
Require Import geometry.
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

  Add Morphism (@bsm CRasCSetoid CRasCSetoid CRasCSetoid)
    with signature (@eq _) ==> (@cs_eq _) ==> (@cs_eq _) ==> (@cs_eq _)
    as gh_mor.
  Proof. intro. exact (@bsm_mor _ _ _ y y (refl_equal _)). Qed.

  Add Morphism finv with signature (@cs_eq _) ==> (@cs_eq _) ==> (@cs_eq _)
    as finv_wd.
  Proof. intros. apply (inv_wd fm); assumption. Qed.

  Definition low: option Time :=
      flip_opt None (ox' oa) (fun x'a => flip_opt None (ox ob) (fun xb =>
        Some (finv x'a xb))).
  Definition high: option Time :=
      flip_opt None (ox oa) (fun xa => flip_opt None (ox' ob) (fun x'b =>
        Some (finv xa x'b))).

  Lemma low_le_high: OCRle (low, high).
  Proof with simpl; auto.
    unfold OCRle, low, high.
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

Section contents.

  Variables
     (fx fy: Flow CRasCSetoid)
     (finvx finvy: OpenRange -> OpenRange -> OpenRange) (* last range is a duration range *)
     (oa ob: OpenSquare).

  Definition f (p: Point) (t: Time): Point := (fx (fst p) t, fy (snd p) t).

  Definition ideal: Prop :=
    exists p: Point, in_osquare p oa /\
    exists t: Time, '0 <= t /\ in_osquare (f p t) ob.

  Definition naive_ideal: Prop :=
    exists p: Point, in_osquare p oa /\
    exists t: Time, in_osquare (f p t) ob.
    (* naive because it doesn't require 0<=t *)

  Definition xflow_range: OpenRange := finvx (fst oa) (fst ob).
  Definition yflow_range: OpenRange := finvy (snd oa) (snd ob).

  Definition naive_decideable: Prop :=
    oranges_overlap (xflow_range, yflow_range).

  Definition practical_decideable (_: unit): Prop :=
    naive_decideable /\
    opt_prop (CRmin_of_upper_bounds (snd (`xflow_range)) (snd (`yflow_range))) CRnonNeg.

  Definition decide_practical eps (_: unit): bool :=
    oranges_overlap_dec eps (xflow_range, yflow_range) &&
    flip_opt true (CRmin_of_upper_bounds (snd (`xflow_range)) (snd (`yflow_range)))
    (CRnonNeg_dec eps).

  Lemma over_decide_practical eps: decide_practical eps >=> practical_decideable.
  Proof with auto.
    unfold decide_practical, practical_decideable, naive_decideable.
    repeat intro.
    destruct H0.
    destruct (andb_false_elim _ _ H).
      apply (over_oranges_overlap eps e)...
    destruct (CRmin_of_upper_bounds (snd (`xflow_range)) (snd (`yflow_range))).
      apply (over_CRnonNeg eps e)...
    discriminate.
  Qed.

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

  Lemma ideal_implies_practical_decideable: ideal -> practical_decideable tt.
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
