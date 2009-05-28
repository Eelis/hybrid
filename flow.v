Require Import c_util.
Require Import geometry.
Require Import CRreal.
Require Import CRexp.
Require Import CRln.
Set Implicit Arguments.
Open Local Scope CR_scope.

(* We require CR because we use it for Time.
 Todo: Take an arbitrary (C)Ring/(C)Field for Time, so that
 the classical development does not need a separate concrete module. *)

Let Time := CRasCSetoid.
Let Duration := NonNegCR.

Record Flow (X: CSetoid): Type :=
  { flow_morphism:> binary_setoid_morphism X Time X
  ; flow_zero: forall x, flow_morphism x ('0) [=] x
  ; flow_additive: forall x t t',
      flow_morphism x (t + t') [=] flow_morphism (flow_morphism x t) t'
  }.

Definition mono (f: Flow CRasCSetoid): Type :=
  sum (forall x, strongly_increasing (f x))
    (forall x, strongly_decreasing (f x)).

Definition range_flow_inv_spec (f: Flow CRasCSetoid)
  (i: OpenRange -> OpenRange -> OpenRange): Prop :=
    forall a p, in_orange a p -> forall b t, in_orange b (f p t) -> in_orange (i a b) t.

Section product_flow.

  Variables (X Y: CSetoid) (fx: Flow X) (fy: Flow Y).

  Let f (xy: ProdCSetoid X Y) (t: Time): ProdCSetoid X Y :=
    (fx (fst xy) t, fy (snd xy) t).

  Let fm: binary_setoid_morphism (ProdCSetoid X Y) CRasCSetoid (ProdCSetoid X Y).
  Proof with auto.
    apply (Build_binary_setoid_morphism _ _ _ f).
    intros.
    destruct a. destruct a'. simpl in *.
    destruct H.
    split; apply bsm_mor...
  Defined.

  Definition product_flow: Flow (ProdCSetoid X Y).
  Proof with auto.
    apply (Build_Flow fm); destruct x; simpl.
    destruct fm. simpl.
      split; apply flow_zero.
    split; apply flow_additive.
  Defined.

End product_flow.

Module constant.
Section contents.

  Definition raw (x: CR) (_: Time): CR := x.

  Definition morphism: binary_setoid_morphism CRasCSetoid CRasCSetoid CRasCSetoid
    := Build_binary_setoid_morphism _ _ _ raw (fun _ _ H _ _ _ => H).

  Definition flow: Flow CRasCSetoid.
    apply (Build_Flow morphism ); reflexivity.
  Defined.

  Let eps: Qpos := (1#100)%Qpos. (* todo: turn into parameter *)

  Definition neg_range: OpenRange.
    exists (Some (-'1), Some (-'1)).
    unfold uncurry. simpl. auto.
  Defined.

  Definition inv (a b: OpenRange): OpenRange :=
    if oranges_overlap_dec eps a b: bool then unbounded_range else neg_range.

  Lemma inv_correct: range_flow_inv_spec flow inv.
  Proof with auto.
    unfold range_flow_inv_spec, inv.
    intros.
    destruct_call oranges_overlap_dec.
    destruct x...
    elimtype False.
    apply n, oranges_share_point with p...
  Qed.

End contents.
End constant.

Module scale.
Section contents.

  Variable s: CR.
  Hypothesis sp: CRpos s.

  Variable f: Flow CRasCSetoid.

  Definition raw (x: CR) (t: Time): CR := f x (s * t).

  Definition morphism: binary_setoid_morphism CRasCSetoid CRasCSetoid CRasCSetoid.
    apply (Build_binary_setoid_morphism _ _ _ raw).
    unfold raw.
    intros.
    apply bsm_wd.
      assumption.
    rewrite H0.
    reflexivity.
  Defined.

  Definition flow: Flow CRasCSetoid.
    apply (Build_Flow morphism); intros; simpl bsm; unfold raw.
      assert (x [=] x) by reflexivity.
      rewrite (bsm_wd f x x H (s * '0) ('0)).
        apply flow_zero.
      apply CRmult_0_r.
    assert (x [=] x) by reflexivity.
    rewrite (bsm_wd f x x H (s * (t + t')) (s * t + s * t')).
      apply flow_additive.
    rewrite (Rmul_comm CR_ring_theory).
    rewrite (Rmul_comm CR_ring_theory s t).
    rewrite (Rmul_comm CR_ring_theory s t').
    apply (Rdistr_l CR_ring_theory).
  Defined.

  Lemma inc: (forall x, strongly_increasing (f x)) ->
    forall x, strongly_increasing (flow x).
  Proof.
    repeat intro. unfold flow. simpl.
    apply X, CRmult_lt_pos_r; assumption.
  Qed.

  Variable old_inv: OpenRange -> OpenRange -> OpenRange.
  Hypothesis old_inv_correct: range_flow_inv_spec f old_inv.

  Lemma CRpos_apart_0 x: CRpos x -> x >< '0.
    right. apply CRpos_lt_0_rev. assumption.
  Defined.

  Definition sinv: CR := CRinv s (CRpos_apart_0 sp).

  Lemma sinv_nonneg: '0 <= sinv.
  Proof.
    apply CRlt_le, CRpos_lt_0_rev, CRinv_pos.
    assumption.
  Qed.

  Definition inv (a b: OpenRange): OpenRange := scale_orange sinv_nonneg (old_inv a b).

  Lemma inv_correct: range_flow_inv_spec flow inv.
  Proof with auto.
    unfold range_flow_inv_spec in *.
    intros.
    unfold inv.
    simpl in H0.
    unfold raw in H0.
    set (old_inv_correct H _ H0).
    clearbody i.
    assert (fst (` (scale_orange sinv_nonneg (old_inv a b))) [=] fst (` (scale_orange sinv_nonneg (old_inv a b)))) by reflexivity.
    assert (snd (` (scale_orange sinv_nonneg (old_inv a b))) [=] snd (` (scale_orange sinv_nonneg (old_inv a b)))) by reflexivity.
    assert (sinv * (s * t) == t).
      rewrite (Rmul_assoc CR_ring_theory).
      unfold sinv.
      rewrite (Rmul_comm CR_ring_theory (CRinv s (CRpos_apart_0 sp))).
      rewrite CRinv_mult.
      apply (Rmul_1_l CR_ring_theory).
    apply (in_orange_wd (scale_orange sinv_nonneg (old_inv a b)) H1 H2 H3).
    apply in_scale_orange...
  Qed.

End contents.
End scale.

Hint Resolve scale.inc.

Module positive_linear.
Section contents.

  Definition morphism: binary_setoid_morphism CRasCSetoid CRasCSetoid CRasCSetoid.
  Proof.
    apply (Build_binary_setoid_morphism _ _ _ (ucFun2 CRplus)).
    intros. rewrite H. rewrite H0. reflexivity.
  Defined.

  Definition f: Flow CRasCSetoid := Build_Flow morphism CRadd_0_r (Radd_assoc CR_ring_theory).

  Definition inv (x x': CR): Time := x' - x.

  Lemma inv_correct x x': f x (inv x x') == x'.
  Proof. intros. symmetry. apply t11. Qed.

  Lemma increasing: forall x : CRasCSetoid, strongly_increasing (f x).
  Proof. repeat intro. apply t1_rev. assumption. Qed.

  Definition mono: mono f := inl increasing.

End contents.
End positive_linear.

Hint Immediate positive_linear.increasing.

Module negative_linear.
Section contents.

  Definition raw (x: CR) (t: Time): CR := x - t.

  Definition morphism: binary_setoid_morphism CRasCSetoid CRasCSetoid CRasCSetoid.
  Proof.
    apply (Build_binary_setoid_morphism _ _ _ raw).
    intros. unfold raw.
    rewrite H. rewrite H0. reflexivity.
  Defined.

  Lemma B x t t': x - (t + t') == x - t - t'.
    intros.    
    rewrite (@Ropp_add _ _ _ _ _ _ _ _ t3 CR_ring_eq_ext CR_ring_theory ).
    apply (Radd_assoc CR_ring_theory).
  Qed.

  Definition f: Flow CRasCSetoid := Build_Flow morphism CRminus_zero B.

  Definition inv (x x': CR): Time := x - x'.

  Lemma inv_correct x x': f x (inv x x') == x'.
    intros.
    unfold f, inv. simpl bsm. unfold raw.
    rewrite <- diff_opp.
    symmetry.
    apply t11.
  Qed.

  Lemma decreasing: forall x : CRasCSetoid, strongly_decreasing (f x).
    repeat intro. simpl. unfold raw.
    apply t1_rev, CRlt_opp_compat.
    assumption.
  Qed.

  Definition mono: mono f := inr decreasing.

End contents.
End negative_linear.
