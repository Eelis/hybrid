Require geometry.
Require Import util c_util.
Require abstract abstraction.

Set Implicit Arguments.

Open Scope CR_scope.

Section contents.

  Variables
    (chs: concrete.System)
    (component: unary_setoid_morphism (concrete.Point chs) CRasCSetoid).

  Add Morphism component with signature (@cs_eq _) ==> (@cs_eq _) as component_mor.
  Proof. intros. apply usm_wd; auto. Qed.

  Variable Region: Set.

  Context
    {Region_eq_dec: EquivDec.EqDec Region eq}
    {regions: ExhaustiveList Region}
    (NoDup_regions: NoDup regions)
    (bounds: Region -> geometry.OpenQRange)
    (select_interval: forall l p, concrete.invariant (l, p) ->
    sig (fun i => geometry.in_orange (bounds i) (component p))).

  Definition in_region (p: concrete.Point chs) (r: Region): Prop :=
    geometry.in_orange (bounds r) (component p).

  Definition in_region_wd x x': x[=]x' -> forall r, in_region x r -> in_region x' r.
  Proof with auto.
    unfold in_region.
    intros.
    apply (@geometry.in_orange_wd (bounds r) (bounds r) ) with (component x)...
    apply (usm_wd component)...
  Qed.

  Definition parameters: abstract.Parameters chs :=
    abstract.Build_Parameters chs _ _ NoDup_regions
      in_region in_region_wd select_interval.

  Definition hints (r r': abstract.Region parameters) (f: flow.Flow (concrete.Point chs)):
    (forall x, strongly_increasing (component ∘ f x)) ->
    option
    (forall p: concrete.Point chs,
     abstract.in_region parameters p r ->
     forall t: flow.Time,
     abstract.in_region parameters (f p t) r' -> t <= ' 0).
  Proof with auto.
    intros.
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
