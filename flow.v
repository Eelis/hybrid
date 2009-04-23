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
    simpl. apply CRle_refl.
  Defined.

  Definition inv (a b: OpenRange): OpenRange :=
    if oranges_overlap_dec eps (a, b) then unbounded_range else neg_range.

  Lemma inv_correct: range_flow_inv_spec flow inv.
  Proof with auto.
    unfold range_flow_inv_spec, inv.
    intros.
    case_eq (oranges_overlap_dec eps (a, b))...
    intros.
    elimtype False.
    apply (over_oranges_overlap eps H1).
    apply oranges_share_point with p...
  Qed.

End contents.
End constant.

Module scale.
Section contents.

  Variable s: CR.
  Hypothesis sp: '0 < s.

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

  Variable old_inv: OpenRange -> OpenRange -> OpenRange.
  Hypothesis old_inv_correct: range_flow_inv_spec f old_inv.

  Definition sinv: CR := CRinv s (Cinright _ _ sp).

  Lemma sinv_nonneg: '0 <= sinv.
  Proof. apply CRlt_le, CRinv_pos. assumption. Qed.

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
      rewrite (Rmul_comm CR_ring_theory (CRinv s (Cinright _ _ sp))).
      rewrite CRinv_mult.
      apply (Rmul_1_l CR_ring_theory).
    apply (in_orange_wd (scale_orange sinv_nonneg (old_inv a b)) H1 H2 H3).
    apply in_scale_orange...
  Qed.

End contents.
End scale.

Module positive_linear.
Section contents.

  Variable r: positive. (* todo: generalize to Qpos, CRpos *)

  Definition raw (x: CR) (t: Time): CR := x + 'r * t.

  Definition morphism: binary_setoid_morphism CRasCSetoid CRasCSetoid CRasCSetoid.
  Proof.
    apply (Build_binary_setoid_morphism _ _ _ raw).
    intros. unfold raw.
    rewrite H. rewrite H0. reflexivity.
  Defined.

  Lemma A x: x + 'r * '0 == x.
    intros.
    rewrite CRmult_0_r.
    apply CRadd_0_r.
  Qed.

  Lemma B x t t': x + 'r * (t + t') == x + 'r * t + 'r * t'.
    intros.
    rewrite (Rmul_comm CR_ring_theory).
    rewrite (Rdistr_l CR_ring_theory).
    rewrite (Radd_assoc CR_ring_theory).
    repeat rewrite (Rmul_comm CR_ring_theory ('r)).
    reflexivity.
  Qed.

  Definition f: Flow CRasCSetoid := Build_Flow morphism A B.

  Definition inv (x x': CR): Time := '(1#r) * (x' - x).

  Lemma inv_correct x x': f x (inv x x') == x'.
    intros.
    unfold f, inv. simpl bsm. unfold raw.
    rewrite (Rmul_assoc CR_ring_theory).
    rewrite CRmult_Qmult.
    rewrite Qmult_inv.
      rewrite (Rmul_1_l CR_ring_theory).
      symmetry. apply t11.
    reflexivity.
  Qed.

  Lemma increasing: forall x : CRasCSetoid, strongly_increasing (f x).
    repeat intro. simpl. unfold raw. apply t1_rev. 
    apply CRmult_lt_pos_r. assumption.
    apply positive_CRpos.
  Qed.

  Definition mono: mono f := inl increasing.

End contents.
End positive_linear.

Module negative_linear.
Section contents.

  Variable r: positive. (* todo: generalize to Qpos, CRpos *)

  Definition raw (x: CR) (t: Time): CR := x - 'r * t.

  Definition morphism: binary_setoid_morphism CRasCSetoid CRasCSetoid CRasCSetoid.
  Proof.
    apply (Build_binary_setoid_morphism _ _ _ raw).
    intros. unfold raw.
    rewrite H. rewrite H0. reflexivity.
  Defined.

  Lemma A x: x - 'r * '0 == x.
  Proof. intros. rewrite CRmult_0_r. apply CRminus_zero. Qed.

  Lemma B x t t': x - 'r * (t + t') == x - 'r * t - 'r * t'.
    intros.    
    rewrite (Rmul_comm CR_ring_theory).
    rewrite (Rdistr_l CR_ring_theory).
    rewrite (Rmul_comm CR_ring_theory t).
    rewrite (Rmul_comm CR_ring_theory t').
    rewrite (@Ropp_add _ _ _ _ _ _ _ _ t3 CR_ring_eq_ext CR_ring_theory ).
    rewrite (Radd_assoc CR_ring_theory).
    reflexivity.
  Qed.

  Definition f: Flow CRasCSetoid := Build_Flow morphism A B.

  Definition inv (x x': CR): Time := '(1#r) * (x - x').

  Lemma inv_correct x x': f x (inv x x') == x'.
    intros.
    unfold f, inv. simpl bsm. unfold raw.
    rewrite (Rmul_assoc CR_ring_theory).
    rewrite CRmult_Qmult.
    rewrite Qmult_inv.
      rewrite (Rmul_1_l CR_ring_theory).
      rewrite <- diff_opp.
      symmetry.
      apply t11.
    reflexivity.
  Qed.

  Lemma decreasing: forall x : CRasCSetoid, strongly_decreasing (f x).
    repeat intro. simpl. unfold raw. apply t1_rev.
    apply CRlt_opp_compat.
    apply CRmult_lt_pos_r.
      assumption.
    apply positive_CRpos.
  Qed.

  Definition mono: mono f := inr decreasing.

End contents.
End negative_linear.

(* todo: move these linear flows to monotonic_flow, since they depend on
flow_range_covers for their range inverse correctness. *)

Module decreasing_exponential.
Section contents.

  Definition raw (x: CR) (t: Time): CR := x * exp (-t).

  Lemma mono: forall x a b, CRpos x -> a < b -> raw x b < raw x a.
  Proof with auto.
    repeat intro.
    unfold raw.
    apply CRmult_lt_pos_r...
    apply exp_inc.
    apply CRlt_opp_compat...
  Qed.

  Lemma raw_lt_compat_l: forall x a b, CRpos x -> a < b -> raw a x < raw b x.
  Proof with auto.
    intros.
    unfold raw.
    apply CRlt_wd with (exp (-x) * a) (exp (-x) * b).
        apply (Rmul_comm CR_ring_theory).
      apply (Rmul_comm CR_ring_theory).
    apply CRmult_lt_pos_r...
    apply CRpos_lt_0.
    apply exp_pos.
  Qed.

  Lemma raw_le_compat_l: forall x a b, a <= b -> raw a x <= raw b x.
  Proof with auto.
    intros.
    unfold raw.
    rewrite (Rmul_comm CR_ring_theory a).
    rewrite (Rmul_comm CR_ring_theory b).
    apply CRmult_le_compat_r...
    apply CRpos_nonNeg.
    apply CRpos_lt_0.
    apply exp_pos.
  Qed.

  Lemma raw_le_inv_r: forall x a b, CRnonNeg x -> raw x b <= raw x a -> a <= b.
  Proof with auto.
    unfold raw.
    intros.
    apply CRle_opp_inv.
    apply (exp_le_inv).
    apply CRmult_le_inv with x...
  Qed.

  Definition morphism: binary_setoid_morphism CRasCSetoid CRasCSetoid CRasCSetoid.
  Proof.
    apply (Build_binary_setoid_morphism _ _ _ raw).
    intros. unfold raw.
    rewrite H. rewrite H0. reflexivity.
  Defined.

  Lemma A x: x * exp (-'0) == x.
    intros.
    rewrite CRopp_0.
    rewrite exp_0.
    rewrite (Rmul_comm CR_ring_theory).
    apply (Rmul_1_l CR_ring_theory).
  Qed.

  Lemma B x t t': x * exp (- (t + t'))[=]x * exp (- t) * exp (- t').
    intros.
    rewrite <- (Rmul_assoc CR_ring_theory).
    rewrite <- exp_sum.
    rewrite (@Ropp_add _ _ _ _ _ _ _ _ t3 CR_ring_eq_ext CR_ring_theory).
    reflexivity.
  Qed.

  Definition f: Flow CRasCSetoid := Build_Flow morphism A B.

  Definition part_inv (x x': CR) (xp: '0 < x) (x'p: '0 < x'): Time := CRln x xp - CRln x' x'p.

  Lemma part_inv_correct (x: CR) (xp: '0 < x) (x': CR) (x'p: '0 < x'):
    raw x (part_inv xp x'p) == x'.
  Proof with auto.
    unfold raw, part_inv.
    intros.
    rewrite <- diff_opp.
    rewrite exp_sum.
    rewrite exp_ln.
    rewrite (Rmul_comm CR_ring_theory x').
    rewrite (Rmul_assoc CR_ring_theory).
    rewrite exp_opp_ln.
    apply (Rmul_1_l CR_ring_theory).
  Qed.

(* b is the upper bound. we now consider what the minimum time required to get from
 [a,...] to [...,b] is.

if b<=0, then [...,b] is totally unreachable.
of course, we can't determine that. we can determine:
- 0<b, then just use part_inv
- dunno, then return None, so infinitely low bound. terrible, but won't be selected often.
- b<0, then -1, because clearly unreachable
 *)

  Let eps: Qpos := (1#1000)%Qpos. (* todo: turn into parameter *)

  Definition dus: Qpos -> forall (x: CR), option (CRpos x).
    intros e x.
    case_eq (CR_epsilon_sign_dec e x); intro.
        exact None.
      exact None.
    exact (Some (CR_epsilon_sign_dec_pos x (existT _ e H))).
  Defined.

  Definition lower (a b: option CR): option Time.
    (* what is the minimum duration that goes from (a, ...) to (..., b) ? *)
  Proof with auto.
    intros a b.
    destruct a as [a |].
      destruct b as [b |].
        destruct (dus eps a).
          destruct (dus eps b).
            apply Some.
            apply (part_inv (CRpos_lt_0_rev c) (CRpos_lt_0_rev c0)).
          (* b not positive *)
          exact None.
        (* a not positive *)
        exact None.
      (* b unbounded, so the second range is (c, ...) *)
      exact None.
    (* a unbounded, so the first range is (..., c) *)
    exact None. (*
    destruct b.
      rename m into b.
      destruct (dus eps b).
        exact None.
      (* b not (known to be) positive *)
      exact None.
    (* b unbounded *)
    exact None. *)
  Defined.

  Hint Resolve CRpos_lt_0_rev exp_pos CRmult_lt_0 CRln_le.

  Lemma lo (p: CR) (a b: option CR) (t: CR):
    OCRle (a, Some p) -> OCRle (Some (raw p t), b) -> OCRle (lower a b, Some t).
  Proof with auto.
    intros.
    destruct a as [a |]...
    destruct b as [b |]...
    simpl.
    destruct (dus eps a)...
    destruct (dus eps b)...
    simpl in H, H0.
    assert ('0 < p). apply CRlt_le_trans with a...
    assert ('0 < raw p t). unfold raw...
    unfold part_inv.
    assert (t == part_inv H1 H2).
      unfold part_inv.
      unfold raw.
      assert ('0 < exp (-t)) by apply exp_pos.
      rewrite (CRln_mult H1 H3 H2).
      rewrite CRln_exp.
      rewrite <- diff_opp.
      rewrite <- t11.
      reflexivity.
    rewrite H3.
    apply t9...
    apply t8...
  Qed.

  Definition upper (a b: option CR): option Time.
    (* what is the maximum duration that goes from (..., a) to (b, ...) ? *)
  Proof with auto.
    intros a b.
    destruct a as [a |].
      destruct b as [b |].
        destruct (dus eps a).
          destruct (dus eps b).
            apply Some.
            apply (part_inv (CRpos_lt_0_rev c) (CRpos_lt_0_rev c0)).
          (* b not positive, so (..., a) to (-c, ...) *)
          exact None.
        (* a not positive *)
        exact None.
      (* b unbounded, so (..., a) to (c, ...) *)
      exact None.
    (* a unbounded *)
    exact None. (*
    destruct b.
      rename m into b.
      destruct (dus eps b).
        exact None.
      (* b not (known to be) positive *)
      exact None.
    (* b unbounded *)
    exact None. *)
  Defined.

  Lemma hi (p: CR) (a b: option CR) (t: CR):
    OCRle (Some p, a) -> OCRle (b, Some (raw p t)) -> OCRle (Some t, upper a b).
  Proof with auto.
    intros.
    destruct a as [a |]...
    destruct b as [b |]...
    simpl.
    destruct (dus eps a)...
    destruct (dus eps b)...
    simpl in H, H0.
    assert ('0 < raw p t). apply CRlt_le_trans with b...
    assert ('0 < p).
      unfold raw in H1.
      assert ('0 < exp (-t) * p).
        apply CRlt_wd with ('0) (p * exp (-t))...
          reflexivity.
        apply (Rmul_comm CR_ring_theory).
      apply (bah H2)...
    unfold part_inv.
    assert (t == part_inv H2 H1).
      unfold part_inv.
      unfold raw.
      assert ('0 < exp (-t)) by apply exp_pos.
      rewrite (CRln_mult H2 H3 H1).
      rewrite CRln_exp.
      rewrite <- diff_opp.
      rewrite <- t11.
      reflexivity.
    rewrite H3.
    apply t9...
    apply t8...
  Qed.

  Lemma lower_le_upper (r r': OpenRange):
    OCRle (lower (fst (`r)) (snd (`r')), upper (snd (`r)) (fst (`r'))).
  Proof with auto.
    destruct r as [[a_lo a_hi] a_le].
    destruct r' as [[b_lo b_hi] b_le].
    simpl proj1_sig. simpl @fst. simpl @snd.
    destruct a_lo as [a_lo |];
    destruct a_hi as [a_hi |];
    destruct b_lo as [b_lo |];
    destruct b_hi as [b_hi |];
    simpl;
    try destruct (dus eps a_lo);
    try destruct (dus eps a_hi);
    try destruct (dus eps b_lo);
    try destruct (dus eps b_hi)...
    apply t9...
    apply t8...
  Qed.

  Definition inv (r r': OpenRange): OpenRange :=
    existT OCRle (lower (fst (`r)) (snd (`r')), upper (snd (`r)) (fst (`r')))
      (lower_le_upper r r').

  Lemma inv_correct: range_flow_inv_spec f inv.
  Proof with auto.
    unfold range_flow_inv_spec, inv.
    intros.
    destruct a as [[a_lo a_hi] a_le].
    destruct b as [[b_lo b_hi] b_le].
    simpl proj1_sig. simpl @fst. simpl @snd.
    unfold in_orange, orange_left, orange_right in *.
    simpl proj1_sig in *. simpl @fst in *. simpl @snd in *.
    destruct H. destruct H0.
    split.
      apply (lo p a_lo b_hi)...
    apply (hi p a_hi b_lo)...
  Qed.

End contents.
End decreasing_exponential.
