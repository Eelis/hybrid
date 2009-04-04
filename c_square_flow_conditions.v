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
    destruct o0; destruct o1; destruct fm; tauto.
  Qed.

  Add Morphism (@bsm CRasCSetoid CRasCSetoid CRasCSetoid)
    with signature (@eq _) ==> (@cs_eq _) ==> (@cs_eq _) ==> (@cs_eq _)
    as gh_mor.
  Proof. intro. exact (@bsm_mor _ _ _ y y (refl_equal _)). Qed.

  Add Morphism finv with signature (@cs_eq _) ==> (@cs_eq _) ==> (@cs_eq _)
    as finv_wd.
  Proof. intros. apply (inv_wd fm); assumption. Qed.

End contents.
End one_axis.

Section contents.

  Variables
     (fx fy: Flow CRasCSetoid)
     (finvx finvy: CR -> CR -> Time)
     (finvx_correct: forall x x', fx x (finvx x x') == x')
     (finvy_correct: forall y y', fy y (finvy y y') == y')
     (fxm: mono fx) (fym: mono fy)
     (oa ob: OpenSquare).

  Definition f (p: Point) (t: Time): Point := (fx (fst p) t, fy (snd p) t).

  Let ox  (s: OpenSquare): option CR := (if fxm then orange_left  else orange_right) (fst s).
  Let ox' (s: OpenSquare): option CR := (if fxm then orange_right else orange_left ) (fst s).
  Let oy  (s: OpenSquare): option CR := (if fym then orange_left  else orange_right) (snd s).
  Let oy' (s: OpenSquare): option CR := (if fym then orange_right else orange_left ) (snd s).

  Let in_ox (s: OpenSquare) (ux: CR): Prop := omle fxm (ox s) (Some ux) /\ omle fxm (Some ux) (ox' s).
  Let in_oy (s: OpenSquare) (uy: CR): Prop := omle fym (oy s) (Some uy) /\ omle fym (Some uy) (oy' s).

  Let omle_x_x' s: omle fxm (ox s) (ox' s).
  Proof. intros [[[c i] d] [[u p] v]]. destruct fxm; auto. Qed.

  Let omle_y_y' s: omle fym (oy s) (oy' s).
  Proof. intros [[[c i] d] [[u p] v]]. destruct fym; auto. Qed.

  Let in_os (s: OpenSquare) (p: Point): Prop :=
    in_ox s (fst p) /\ in_oy s (snd p).
    (* expressed in terms of the mono accessors, makes reasoning easier *)

  Definition in_osquare_alt s p: in_osquare p s <-> in_os s p.
    unfold in_osquare, in_os, in_ox, in_oy.
    intros [[c u] [d v]] [px py].
    subst ox ox' oy oy'.
    simpl. unfold in_orange.
    destruct fxm; destruct fym; tauto.
  Qed.

  Definition oideal: Prop :=
    exists p: Point, in_osquare p oa /\
    exists t: Time, '0 <= t /\ in_osquare (f p t) ob.

  Definition onaive_ideal: Prop :=
    exists p: Point, in_osquare p oa /\
    exists t: Time, in_osquare (f p t) ob.
    (* naive because it doesn't require 0<=t *)

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

  Corollary ideal_implies_naive_decideable: oideal -> onaive_decideable.
  Proof.
    intro. apply onaive_ideal_implies_onaive_decideable.
    destruct H. destruct H. destruct H0. destruct H0.
    unfold onaive_ideal. eauto.
  Qed.

  (* naive_decideable <-> naive_ideal  should be provable. We had a proof
   of it before we made square bounds optional. It should be routine (but some
   work) to adapt that proof (which can be found in the darcs history). *)

  Definition opractical_decideable: Prop :=
    onaive_decideable /\
    omle fxm (ox oa) (ox' ob) /\ omle fym (oy oa) (oy' ob).
        (* This is weak enough to be implied by ideal, but not strong
          enough to get the reverse implication. (The latter claim is not
          yet proved.) For now, it's an acceptable compromise. *)

    (* Todo: can we define a decideable condition equivalent
     to (non-naive) ideal? *)

Lemma omle_trans f (m: mono f) (x: option CR) (y: CR):
  omle m x (Some y) -> forall z, omle m (Some y) z -> omle m x z.
Proof with auto.
  intros.
  unfold omle in *.
  destruct m.
    destruct x; destruct z...
    apply CRle_trans with m0...
    apply CRle_trans with y...
  destruct x; destruct z...
  apply CRle_trans with m0...
  apply CRle_trans with y...
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

  Definition opractical_dec eps (_ : unit) : bool :=
    onaive_dec eps () &&
    omle_dec fxm eps (ox oa) (ox' ob) &&
    omle_dec fym eps (oy oa) (oy' ob).

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
