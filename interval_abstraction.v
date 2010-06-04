Require Import util c_util stability.
Require geometry abstract abstract_cont_trans_over.
Require Import Morphisms.

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
    DN (sig (fun i => geometry.in_orange (bounds i) (component p)))).

  Definition in_region (p: concrete.Point chs) (r: Region): Prop :=
    geometry.in_orange (bounds r) (component p).

  Instance in_region_mor: Morphism (@cs_eq _ ==> eq ==> iff) in_region.
  Proof with auto.
    unfold in_region. repeat intro.
    apply geometry.in_orange_mor.
      subst. split...
    rewrite H...
  Qed.

  Definition space: abstract.Space chs :=
    abstract.Build_Space chs _ _ NoDup_regions
      in_region_mor select_interval.

  Definition hints (l: concrete.Location chs) (r r': abstract.Region space) (E: r <> r'):
    (forall x, strongly_increasing (component ∘ concrete.flow chs l x)) ->
    option (abstract_cont_trans_over.strong_redundant space l E).
  Proof with auto.
    intros.
    unfold abstract_cont_trans_over.strong_redundant, containers.In.
    simpl abstract.in_region.
    unfold in_region.
    destruct (bounds r) as [[ci_lo ci_hi] ci_le].
    destruct (bounds r') as [[ci'_lo ci'_hi] ci'_le].
    unfold geometry.in_orange, geometry.orange_left, geometry.orange_right.
    simpl @fst. simpl @snd.
    destruct ci_lo; [ | exact None].
    destruct ci'_hi; [ | exact None].
    destruct (Qeq_dec q q0) as [A|B]; [ | exact None].
    apply Some.
    intros p [H0 H4] t [H1 H5].
    apply (strongly_increasing_inv_mild (X p)).
    unfold Basics.compose.
    rewrite flow.flow_zero.
    apply CRle_trans with ('q)...
    rewrite A...
  Defined.

End contents.
