Require Import List.
Require Import c_util util list_util.
Require Import CSetoids CRreal.
Require Import flow.
Require concrete abstract.
Set Implicit Arguments.
Open Local Scope CR_scope.
Require Import EquivDec.

Section contents.

  Variable (chs: concrete.System) (ap: abstract.Parameters chs).

  Let Location := concrete.Location chs.
  Let Point := concrete.Point chs.
  Let c_State := concrete.State chs.
  Let State := abstract.State ap.

  (* Recall from the discussion in abstract.v about continuous transitions
  that the respect condition was specifically formulated such that the
  abstract continuous transition function could cleverly omit "silly" regions from
  its result list (such as the one corresponding to the transition from [1,2]
  to [0,1] in the example), thus avoiding undesireable abstract flow in the
  "wrong" direction.

  We now provide one systematic way of producing such functions. More
  specifically, this module constructs such a function when given two things:
  (1) an overestimator for the existance of a concrete continuous transition
  between points in a given pair of regions; and (2) a set of "hints". We will
  describe both of these in more detail.

  The overestimator must have the following type: *)

  Definition condition l r r': Prop := exists p q,
    abstract.in_region ap p r /\
    abstract.in_region ap q r' /\
    concrete.cont_trans (l, p) (l, q).

  Variable condition_overestimator: overestimator condition.

  (* Thus, it estimates whether there is a continuous transition from a point in the
  source region, to a point in the target region.

  By itself, this would be enough to define an abstract continuous transition
  function of the type described earlier: given a location and source region, simply
  start with an exhaustive list of all regions, and filter out those for which the
  overestimator returns true.

  However, this would mean that in the example described, the resulting list would
  include [0,1] given source region [1,2], because the overestimator would
  have to return true given these two regions.

  It is for this reason that we additionally take a set of optional "hints". A hint is
  an proof showing that the only points in a given destination region
  one can flow to from a given source region, actually still lie in the source region:
  *)

  Definition Hint (l: Location) (r r': abstract.Region ap): Set :=
    forall p, abstract.in_region ap p r ->
      forall t, '0 <= t -> abstract.in_region ap (concrete.flow chs l p t) r' ->
        abstract.in_region ap (concrete.flow chs l p t) r.

  Variable hints: forall (l: Location) (r r': abstract.Region ap),
    r <> r' -> option (Hint l r r').

  (* Before we proceed to define the abstract continuous transition function,
   we first put the hints in a more convenient form in which the region
   inequality is integrated in the optionality: *)

  Definition hints' (l: Location) (r r': abstract.Region ap):
    option (forall p, abstract.in_region ap p r ->
     forall t, '0 <= t -> abstract.in_region ap (concrete.flow chs l p t) r' ->
       abstract.in_region ap (concrete.flow chs l p t) r) :=
    match r == r' with
    | left _ => None
    | right E => hints l E
    end.

  (* We now define the abstract continuous transition function, which
   will omit pointless inclusion of "redundant" regions, as indicated by the hints,
   as follows: *)

  Definition raw_cont_trans (s : State) : list (abstract.Region ap) :=
    let (l, r_src) := s in filter
      (fun r_dst => overestimation_bool (condition_overestimator l r_src r_dst) &&
        negb (hints' l r_src r_dst))
      (abstract.regions ap).

  (* To show that raw_cont_trans satisfies abstract.ContRespect, we
   will need that it is reflexive (since that shows that the omitted transitions
   really are redundant). *)

  Lemma cont_refl l r p: abstract.in_region ap p r -> concrete.invariant (l, p) ->
    In r (raw_cont_trans (l, r)).
  Proof with auto.
    intros.
    apply in_filter...
    apply andb_true_intro.
    split.
      apply overestimation_true.
      simpl.
      exists p. exists p.
      repeat split...
      exists NonNegCR_zero.
      split.
        intros.
        simpl.
        rewrite (curry_eq concrete.invariant).
        assert ('0 [=] t). apply (snd (CRle_def ('0) t))...
        rewrite <- H3.
        rewrite flow_zero...
      simpl.
      rewrite flow_zero...
    simpl.
    unfold hints'.
    destruct (equiv_dec r r)...
    intuition.
  Qed.

  (* Respect is now proved as follows. *)

  Lemma respects_cont s: abstract.ContRespect s (raw_cont_trans s).
  Proof with auto with real.
    intros [l r] p rin p' [d [inv f]].
    assert (concrete.invariant (l, p')).
      rewrite (curry_eq concrete.invariant).
      rewrite <- f.
      apply inv...
      apply -> CRnonNeg_le_zero...
    destruct (abstract.select_region ap l p' H) as [r' rin'].
    case_eq (hints' l r r'); intros.
      exists r.
      split.
        rewrite <- f.
        apply i...
          apply -> CRnonNeg_le_zero...
        rewrite f...
      apply cont_refl with p...
      rewrite (curry_eq concrete.invariant).
      rewrite <- (flow_zero (concrete.flow chs l) p).
      apply inv...
      apply -> CRnonNeg_le_zero...
    exists r'.
    split...
    unfold raw_cont_trans.
    apply in_filter...
    apply andb_true_intro.
    split.
      apply overestimation_true.
      exists p.
      eauto 10.
    rewrite H0...
  Qed.

  (* And with that, we can form the sigma-decorated definition using Program,
   using respects_cont in the generated obligation. *)

  Program Definition cont_trans: forall s: State, sig
    (fun l: list (abstract.Region ap) => LazyProp (NoDup l /\ abstract.ContRespect s l)) :=
    raw_cont_trans.

  Next Obligation. Proof with auto.
    split.
      unfold raw_cont_trans.
      destruct x.
      apply NoDup_filter, (abstract.NoDup_regions ap).
    apply respects_cont.
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

  Definition StrongHint l r r': Set :=
    forall p: Point, abstract.in_region ap p r ->
      forall t: Time, abstract.in_region ap (concrete.flow chs l p t) r' ->
        t <= '0.

  (* Whereas Hint merely says that the destination point lies in the source region,
   StrongHint says that the flow duration is nonpositive. Since flow durations
   are always nonnegative, this means that the duration is zero. This then implies
   that the destination point /is/ the source point, which is a stronger property that
   is no longer relative to any particular set of abstraction parameters. Hence, we
   trivially get that these stronger kinds of hints are "upward" convertible. We will
   show this in a moment, but first show that StrongHints can easily be
   converted to Hints: *)

  Lemma weaken_hint l r r': StrongHint l r r' -> Hint l r r'.
  Proof with eauto.
    repeat intro.
    assert (t [=] '0). apply (CRle_def t ('0))...
    rewrite H3, flow_zero...
  Qed.

  Definition weaken_hints (H: forall l r r', r <> r' -> option (StrongHint l r r')) l r r' (E: r <> r'): option (Hint l r r') :=
    option_map (@weaken_hint l r r') (H l r r' E).

End contents.

(* For the sake of exposition (this result is not used anywhere else in the
development) we show that strong hints support "upward conversion". That is,
that a StrongHint for a set of abstraction parameters is convertible to a
StrongHint for the product of those abstraction parameters with another set of
abstraction parameters. *)

Section strong_upward.

  Variables
    (chs: concrete.System)
    (ap_x ap_y: abstract.Parameters chs).

  Definition ap := abstract.param_prod ap_x ap_y.

  Definition lift_StrongHint (l: concrete.Location chs) (r r': abstract.Region ap)
    (h: StrongHint ap_x l (fst r) (fst r')): StrongHint ap l r r' :=
    fun p A t B => h _ (fst A) _ (fst B).

End strong_upward.
