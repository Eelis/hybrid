Set Automatic Coercions Import.

Require Import c_util.
Require Import util.
Require Import geometry.
Require Import CRreal.
Require Import CRexp.
Require Import CRln.
Require Import Morphisms.
Set Implicit Arguments.
Open Local Scope CR_scope.

(* We require CR because we use it for Time.
 Todo: Take an arbitrary (C)Ring/(C)Field for Time, so that
 the classical development does not need a separate concrete module. *)

Let Time := CRasCSetoid.
Let Duration := NonNegCR.

Record Flow (X: CSetoid): Type :=
  { flow_morphism:> morpher (@st_eq X ==> @st_eq Time ==> @st_eq X)%signature
  ; flow_zero: forall x, flow_morphism x 0 [=] x
  ; flow_additive: forall x t t',
      flow_morphism x (t + t') [=] flow_morphism (flow_morphism x t) t'
  }.

Definition mono (f: Flow CRasCSetoid): Type :=
  ((forall x, strongly_increasing (f x)) + (forall x, strongly_decreasing (f x)))%type.

Definition range_flow_inv_spec (f: Flow CRasCSetoid)
  (i: OpenRange -> OpenRange -> OpenRange): Prop :=
    forall a p, in_orange a p -> forall b t, in_orange b (f p t) -> in_orange (i a b) t.

Hint Unfold range_flow_inv_spec.

Obligation Tactic := idtac.

Program Definition product_flow (X Y: CSetoid) (fx: Flow X) (fy: Flow Y):
  Flow (ProdCSetoid X Y) :=
    Build_Flow _ (fun xy t => (fx (fst xy) t, fy (snd xy) t)) _ _.

Next Obligation.
  intros X Y fx fy [s s0] [s1 s2] [A B] x y H0.
  split; [rewrite A | rewrite B]; rewrite H0; reflexivity.
Qed.

Next Obligation. destruct x. split; apply flow_zero. Qed.
Next Obligation. destruct x. split; apply flow_additive. Qed.

Module constant.
Section contents.

  Program Definition flow: Flow CRasCSetoid := Build_Flow _ (fun x _ => x) _ _.

  Next Obligation. exact (fun _ _ H _ _ _ => H). Qed.
  Next Obligation. reflexivity. Qed.
  Next Obligation. reflexivity. Qed.

  Let eps: Qpos := (1#100)%Qpos. (* todo: turn into parameter *)

  Definition neg_range: OpenRange.
    exists (Some (-'1%Q), Some (-'1%Q)).
    unfold uncurry. simpl. auto.
  Defined.

  Definition inv (a b: OpenRange): OpenRange :=
    if overestimate_oranges_overlap eps a b: bool then unbounded_range else neg_range.

  Lemma inv_correct: range_flow_inv_spec flow inv.
  Proof with auto.
    unfold range_flow_inv_spec, inv.
    intros.
    destruct_call overestimate_oranges_overlap.
    destruct x...
    elimtype False.
    apply n, oranges_share_point with p...
  Qed.

End contents.
End constant.

Module scale.
Section contents.

  Variables (s: CR) (sp: CRpos s) (f: Flow CRasCSetoid).

  Program Definition flow: Flow CRasCSetoid :=
    Build_Flow _ (fun x t => f x (s * t)) _ _.

  Next Obligation. intros a a' e b b' e'. rewrite e, e'. reflexivity. Qed.

  Next Obligation.
    intros. unfold morpher_to_func, proj1_sig.
    rewrite CRmult_0_r. apply flow_zero.
  Qed.

  Next Obligation.
    intros.
    unfold morpher_to_func at 1 3 5, proj1_sig.
    rewrite
      <- flow_additive,
      (Rmul_comm CR_ring_theory),
      (Rmul_comm CR_ring_theory s t),
      (Rmul_comm CR_ring_theory s t'),
      (Rdistr_l CR_ring_theory).
    reflexivity.
  Qed.

  Lemma inc: (forall x, strongly_increasing (f x)) ->
    forall x, strongly_increasing (flow x).
  Proof.
    repeat intro. unfold flow. simpl.
    apply X, CRmult_lt_pos_r; assumption.
  Qed.

  Variable old_inv: OpenRange -> OpenRange -> OpenRange.
  Hypothesis old_inv_correct: range_flow_inv_spec f old_inv.

  Lemma CRpos_apart_0 x: CRpos x -> x >< 0.
    right. apply CRpos_lt_0_rev. assumption.
  Defined.

  Definition sinv: CR := CRinvT s (CRpos_apart_0 sp).

  Lemma sinv_nonneg: 0 <= sinv.
  Proof.
    apply CRlt_le.
    apply CRpos_lt_0_rev.
    unfold sinv.
    apply CRinvT_pos.
    assumption.
  Qed.

  Definition inv (a b: OpenRange): OpenRange := scale_orange sinv_nonneg (old_inv a b).

  Lemma inv_correct: range_flow_inv_spec flow inv.
  Proof with auto.
    unfold range_flow_inv_spec in *.
    intros.
    unfold inv.
    simpl in H0.
    set (old_inv_correct H _ H0).
    clearbody i.
    assert (fst (` (scale_orange sinv_nonneg (old_inv a b))) [=] fst (` (scale_orange sinv_nonneg (old_inv a b)))) by reflexivity.
    assert (snd (` (scale_orange sinv_nonneg (old_inv a b))) [=] snd (` (scale_orange sinv_nonneg (old_inv a b)))) by reflexivity.
    assert (sinv * (s * t) == t).
      rewrite (Rmul_assoc CR_ring_theory).
      unfold sinv.
      rewrite (Rmul_comm CR_ring_theory (CRinvT s _)).
      unfold CRinv.
      rewrite (CRinvT_mult).
      apply (Rmul_1_l CR_ring_theory).
    rewrite <- H3. (* todo: this takes ridiculously long *)
    apply in_scale_orange...
  Qed.

End contents.
End scale.

Hint Resolve scale.inc scale.inv_correct.

Module positive_linear.
Section contents.

  Program Definition f: Flow CRasCSetoid :=
    Build_Flow _ (ucFun2 CRplus_uc) CRadd_0_r (Radd_assoc CR_ring_theory).

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

  Let B x t t': x - (t + t') == x - t - t'.
    intros.    
    rewrite (@Ropp_add _ _ _ _ _ _ _ _ t3 CR_ring_eq_ext CR_ring_theory ).
    apply (Radd_assoc CR_ring_theory).
  Qed.

  Program Definition f: Flow CRasCSetoid :=
    Build_Flow _ (fun x t => x - t) CRminus_zero B.

  Definition inv (x x': CR): Time := x - x'.

  Lemma inv_correct x x': f x (inv x x') == x'.
    intros.
    unfold f, inv.
    simpl morpher_to_func.
    rewrite <- diff_opp.
    symmetry.
    apply t11.
  Qed.

  Lemma decreasing: forall x : CRasCSetoid, strongly_decreasing (f x).
    repeat intro. simpl.
    apply t1_rev, CRlt_opp_compat.
    assumption.
  Qed.

  Definition mono: mono f := inr decreasing.

End contents.
End negative_linear.

Require Import vector_setoid.
Require Import VecEq.

Lemma Vforall2n_aux_inv (A B: Type) (R: A -> B -> Prop) n (v: vector A n) m (w: vector B m):
  Vforall2n_aux R v w -> forall i (p: lt i n) (q: lt i m), R (Vnth v p) (Vnth w q).
Admitted. (*
Proof.
  induction v; destruct w; simpl; intros; intuition.
    elimtype False.
    apply (lt_n_O _ p).
  destruct i; auto.
Qed. *)

Definition eq_vec_inv (T: Type) (R: relation T) n (x y: vector T n) (e: eq_vec R x y)
  i (p: (i < n)%nat): R (Vnth x p) (Vnth y p)
  := Vforall2n_aux_inv _ _ _ e p p.

(* Todo: Move the above two elsewhere. *)

Section vector_flow.

  Variable n : nat.
  Variable X : CSetoid. 
  Variable vec_f : vector (Flow X) n.

  Let f (vec_x : vecCSetoid X n) (t : Time) : vecCSetoid X n :=
    let flow_dim i ip :=
      let f := Vnth vec_f ip in
      let x := Vnth vec_x ip in
        f x t
    in
      Vbuild flow_dim.

  Program Definition vector_flow : Flow (vecCSetoid X n) :=
    Build_Flow _ f _ _.

  Next Obligation. (* well-defined-ness *)
    do 6 intro.
    apply Veq_vec_nth. intros.
    unfold f.
    repeat rewrite Vbuild_nth.
    unfold morpher_to_func.
    rewrite (eq_vec_inv (@st_eq _) x y H).
    rewrite H0.
    reflexivity.
  Qed.

  Next Obligation. (* flow_zero *)
    apply Veq_vec_nth. intros. unfold f.
    repeat rewrite Vbuild_nth. apply flow_zero.
  Qed.

  Next Obligation. (* flow_additive *)
    apply Veq_vec_nth. intros. unfold f.
    repeat rewrite Vbuild_nth. apply flow_additive.
  Qed.

End vector_flow.
