Require Import c_util.
Require Import c_geometry.
Require Import CRreal.
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

Module pos_linear_flow.
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

  Definition flow: Flow CRasCSetoid := Build_Flow morphism A B.

  Definition inv (x x': CR): Time := '(1#r) * (x' - x).

  Lemma inv_correct x x': flow x (inv x x') == x'.
    intros.
    unfold flow, inv. simpl bsm. unfold raw.
    rewrite (Rmul_assoc CR_ring_theory).
    rewrite CRmult_Qmult.
    rewrite Qmult_inv.
      rewrite (Rmul_1_l CR_ring_theory).
      symmetry. apply t11.
    reflexivity.
  Qed.

  Lemma increasing: forall x : CRasCSetoid, strongly_increasing (flow x).
    repeat intro. simpl. unfold raw. apply t1_rev. 
    apply CRmult_lt_pos_r.
      assumption.
    apply positive_CRpos.
  Qed.

  Definition mono: mono flow := inl increasing.

End contents.
End pos_linear_flow.

Module neg_linear_flow.
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

  Definition flow: Flow CRasCSetoid := Build_Flow morphism A B.

  Definition inv (x x': CR): Time := '(1#r) * (x - x').

  Lemma inv_correct x x': flow x (inv x x') == x'.
    intros.
    unfold flow, inv. simpl bsm. unfold raw.
    rewrite (Rmul_assoc CR_ring_theory).
    rewrite CRmult_Qmult.
    rewrite Qmult_inv.
      rewrite (Rmul_1_l CR_ring_theory).
      rewrite <- diff_opp.
      symmetry.
      apply t11.
    reflexivity.
  Qed.

  Lemma decreasing: forall x : CRasCSetoid, strongly_decreasing (flow x).
    repeat intro. simpl. unfold raw. apply t1_rev.
    apply CRlt_opp_compat.
    apply CRmult_lt_pos_r.
      assumption.
    apply positive_CRpos.
  Qed.

  Definition mono: mono flow := inr decreasing.

End contents.
End neg_linear_flow.

(* todo: move these linear flows to monotonic_flow, since they depend on
flow_range_covers for their range inverse correctness. *)
