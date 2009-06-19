Require geometry.
Require Import util c_util.
Require abstract hinted_abstract_continuous_transitions.

Set Implicit Arguments.

Open Scope CR_scope.

Section contents.

  Variables
    (chs: concrete.System)
    (component: morpher (@cs_eq (concrete.Point chs) ==> @cs_eq CRasCSetoid)%signature)
    (Region: Set).

  Context
    {Region_eq_dec: EquivDec.EqDec Region eq}
    {regions: ExhaustiveList Region}
    (NoDup_regions: NoDup regions)
    (bounds: Region -> geometry.OpenQRange)
    (select_interval: forall l p, concrete.invariant (l, p) ->
    sig (fun i => geometry.in_orange (bounds i) (component p))).

  Definition in_region (p: concrete.Point chs) (r: Region): Prop :=
    geometry.in_orange (bounds r) (component p).

  Instance in_region_mor: Morphism (@cs_eq _ ==> eq ==> iff) in_region.
  Proof with auto.
    unfold in_region. repeat intro.
    apply geometry.in_orange_mor.
      subst. split...
    rewrite H...
  Qed.

  Definition parameters: abstract.Parameters chs :=
    abstract.Build_Parameters chs _ _ NoDup_regions
      in_region_mor select_interval.

  Definition hints (r r': abstract.Region parameters) (l: concrete.Location chs):
    (forall x, strongly_increasing (component ∘ concrete.flow chs l x)) ->
    option (hinted_abstract_continuous_transitions.StrongHint parameters l r r').
  Proof with auto.
    intros.
    unfold hinted_abstract_continuous_transitions.StrongHint.
    simpl abstract.in_region.
    unfold in_region.
    destruct (bounds r) as [[ci_lo ci_hi] ci_le].
    destruct (bounds r') as [[ci'_lo ci'_hi] ci'_le].
    unfold geometry.in_orange, geometry.orange_left, geometry.orange_right.
    simpl @fst. simpl @snd.
    destruct ci_lo; [idtac | exact None].
    destruct ci'_hi; [idtac | exact None].
    destruct (Qeq_dec q q0) as [A|B]; [idtac | exact None].
    apply Some.
    intros p [H0 H4] t [H1 H5].
    apply (strongly_increasing_inv_mild (X p)).
    unfold compose.
    rewrite flow.flow_zero.
    apply CRle_trans with ('q)...
    rewrite A...
  Defined.

End contents.
