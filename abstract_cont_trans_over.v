Set Automatic Coercions Import.

Require Import List.
Require Import c_util util list_util stability containers.
Require Import CSetoids CRreal.
Require Import flow.
Require concrete abstract.
Set Implicit Arguments.
Open Local Scope CR_scope.
Require Import EquivDec.

Module c := concrete.
Module a := abstract.

Section contents.

  Variable (chs: concrete.System) (ap: abstract.Space chs).

  Definition substantial_cont_trans (l: c.Location chs): relation (a.Region ap)
    := fun r r' => exists p q, p ∈ r /\ q ∈ r' /\ ~ q ∈ r /\ c.can_flow chs l p q.

  Hint Unfold substantial_cont_trans.

  Program Definition cont_sharing_overestimator_from_substantial_overestimator (x: overestimator substantial_cont_trans):
    a.sharing_transition_overestimator ap (@concrete.cont_trans _) :=
    fun y => map (pair (fst y)) (filter (fun z => (z == snd y) ||
	  overestimation_bool (x (fst y) (snd y) z)) exhaustive_list).
  Next Obligation. Proof with auto.
    split.
      apply NoDup_map...
        congruence.
      apply NoDup_filter...
      apply a.NoDup_regions...
    intros [l s] [H0 [[l0 s0] [[H1 H4] [H2 H5]]]].
    unfold util.flip, In, predicate_container in H2.
    destruct y as (l', r).
    apply (DN_bind (DN_decision (s ∈ r))).
    intro.
    simpl in H1, H2. repeat subst.
    destruct H3.
      apply DN_return.
      exists (l, r).
      split. split...
      apply in_map. apply in_filter...
      apply orb_true_intro.
      left. apply show_unsumbool. reflexivity.
    apply (DN_fmap (a.regions_cover ap _ _ H0)).
    intros [r' i].
    exists (l, r').
    split. split...
    apply in_map, in_filter...
    apply orb_true_intro.
    destruct (a.Region_eq_dec ap r r'); [left | right].
      apply show_unsumbool.
      rewrite e. reflexivity.
    apply overestimation_true.
    simpl.
    unfold substantial_cont_trans.
    eauto 20.
  Qed.

  Variable simple_overestimator: overestimator (abstract.cont_trans ap).

  Definition redundant (l: c.Location chs) (r r': abstract.Region ap) (H: r <> r'): Prop :=
    forall p, p ∈ r ->
      forall t, 0 <= t -> concrete.flow chs l p t ∈ r' ->
        concrete.flow chs l p t ∈ r.

  Variable under_redundant: underestimator redundant.

  (* Before we proceed to define the abstract continuous transition function,
   we first put the hints in a more convenient form in which the region
   inequality is integrated in the optionality: *)

  Definition hints (l: c.Location chs) (r r': abstract.Region ap):
    option (forall p, p ∈ r -> forall t, 0 <= t -> concrete.flow chs l p t ∈ r' -> concrete.flow chs l p t ∈ r) :=
    match r == r' with
    | left _ => None
    | right E => under_redundant l E
    end.

  Program Definition cont_trans l r r': overestimation (substantial_cont_trans l r r') :=
    (simple_overestimator l r r': bool) && negb (hints l r r').

  Hint Unfold abstract.cont_trans.

  Next Obligation. Proof with eauto 20.
    intros [x [x0 [H0 [H1 [H2 H3]]]]].
    apply andb_false_elim in H.
    destruct H.
      apply overestimation_false in e...
    destruct hints.
      destruct H3. destruct H. destruct x1.
      rewrite <- H3 in H2.
      apply H2.
      simpl proj1_sig.
      apply (i x H0 x1)...
        apply (CRnonNeg_le_zero x1)...
      rewrite H3...
    discriminate.
  Qed.

  (* This concludes the primary contents of this module. Now follow a few more
   notes and utilities about hints.

  First, note that this module takes hints as given, saying nothing about how
  clients are expected to actually construct them. Some utilities for that can
  be found in interval_spec.v. We /can/ however easily make things a bit
  easier by recognizing that there is a stronger notion of Hint that composes
  better.

  Hint is sufficiently strong to support the above development, but is actually rather
  weak. This is generally a good thing in interfaces, but Hint is so weak that
  when using abstraction parameter sets combined with param_prod (from
  abstract.v), hints for the component parameter sets don't necessarily translate
  into hints for the composite parameter set (whose regions are intersections of
  regions of the component parameter sets). After all, just because destination
  points in a destination region are contained in a source region in one
  set of abstraction parameters, doesn't mean this automatically also holds for
  intersections of these regions with regions from another set of abstraction
  parameters. (Todo: Shouldn't be hard to prove, though it could be a bit of work,
  since one would need to construct a counterexample concrete system.)

  However, in some cases, one can actually prove a stronger kind of Hint
  which /does/ support such "upward" conversion:
  *)

  Definition strong_redundant l (r r': a.Region ap) (H: r <> r'): Prop :=
    forall p: c.Point chs, p ∈ r ->
      forall t: Time, concrete.flow chs l p t ∈ r' -> t <= 0.

  (* Whereas Hint merely says that the destination point lies in the source region,
   StrongHint says that the flow duration is nonpositive. Since flow durations
   are always nonnegative, this means that the duration is zero. This then implies
   that the destination point /is/ the source point, which is a stronger property that
   is no longer relative to any particular set of abstraction parameters. Hence, we
   trivially get that these stronger kinds of hints are "upward" convertible. We will
   show this in a moment, but first show that StrongHints can easily be
   converted to Hints: *)

  Lemma weaken_hint l r r' (H: r <> r'): strong_redundant l H -> redundant l H.
  Proof with eauto.
    repeat intro.
    assert (t [=] 0). apply (CRle_def t 0)...
    rewrite H4, flow_zero...
  Qed.

  Definition weaken_hints (H: forall l r r' (H: r <> r'), option (strong_redundant l H)) l r r' (E: r <> r'): option (redundant l E) :=
    option_map (@weaken_hint l r r' E) (H l r r' E).

End contents.

(* For the sake of exposition (this result is not used anywhere else in the
development) we show that strong hints support "upward conversion". That is,
that a StrongHint for a set of abstraction parameters is convertible to a
StrongHint for the product of those abstraction parameters with another set of
abstraction parameters. *)

Section strong_upward.

  Variables
    (chs: concrete.System)
    (ap_x ap_y: abstract.Space chs).

  Definition ap := abstract.prod_space ap_x ap_y.

  Definition lift_strong_redundant (l: concrete.Location chs) (r r': abstract.Region ap) (H: fst r <> fst r') (H0: r <> r')
    (h: strong_redundant ap_x l H): strong_redundant ap l H0 :=
    fun p A t B => h _ (fst A) _ (fst B).

End strong_upward.
