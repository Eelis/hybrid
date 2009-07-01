Require Import reachability.
Require Import List Bool.
Require Import util list_util stability.
Require Import CSetoids.
Require Import Morphisms.
Set Implicit Arguments.
Require EquivDec.
Require concrete.

Section contents.

  Variable chs: concrete.System.

  Record Parameters: Type :=
    { Region: Set
    ; Region_eq_dec: EquivDec.EqDec Region eq
    ; regions: ExhaustiveList Region
    ; NoDup_regions: NoDup regions
    ; in_region: concrete.Point chs -> Region -> Prop
    ; in_region_mor: Morphism (@cs_eq _ ==> eq ==> iff) in_region
    ; regions_cover: forall l p, concrete.invariant (l, p) -> DN (sig (in_region p))
    }.

  Existing Instance Region_eq_dec.
  Existing Instance regions.
  Existing Instance in_region_mor.

  Section param_stuff.

    Variable p: Parameters.

    Definition State := (concrete.Location chs * Region p)%type.

    Definition region: State -> Region p := snd.
    Definition location: State -> concrete.Location chs := fst.

    Definition states: ExhaustiveList State := @ExhaustivePairList (concrete.Location chs) (Region p) _ _.

    Lemma NoDup_states: NoDup (regions p) -> NoDup states.
    Proof. apply NoDup_ExhaustivePairList, concrete.NoDup_locations. Qed.

  End param_stuff.

  (* Given two sets of abstraction parameters, we can combine these to make
   finer-grained abstraction parameters where each region corresponds to the
   intersection of two regions of the respective abstraction parameters.

   For instance, for a hybrid system whose continuous state space is the plane,
   we could first define abstraction parameters with regions corresponding to X
   intervals, then define abstraction parameters with regions corresponding to
   Y intervals, and then finally combine these using param_prod below to
   produce abstraction parameters with regions corresponding to squares. *)

  Section param_prod.

    Variables ap ap': Parameters.

    Let in_region p r := in_region ap p (fst r) /\ in_region ap' p (snd r).

    Let in_region_mor: Morphism (@cs_eq _ ==> eq ==> iff) in_region.
    Proof. unfold in_region. intros x x' e r r' e'. rewrite e, e'. split; auto. Qed.

    Let regions_cover: forall (l : concrete.Location chs) (p : concrete.Point chs),
      concrete.invariant (l, p) -> DN (sig (in_region p)).
    Proof with auto.
      intros.
      apply (DN_bind (regions_cover ap _ _ H)). intro.
      apply (DN_bind (regions_cover ap' _ _ H)). intro.
      apply DN_return.
      destruct H0.
      destruct H1.
      exists (x, x0).
      split; assumption.
    Defined. (* written with Program and monad notation, this should be much clearer *)

    Definition param_prod: Parameters := Build_Parameters  _ _
      (NoDup_ExhaustivePairList (NoDup_regions ap) (NoDup_regions ap'))
      in_region_mor regions_cover.

  End param_prod.

  Variable ap: Parameters.

  Definition ContRespect (s: State ap) (l: list (Region ap)): Prop :=
     forall p, in_region ap p (region s) ->
     forall q, concrete.can_flow chs (location s) p q ->
       DN (exists r', in_region ap q r' /\ In r' l).

  (* Note that this is no longer the traditional

      "there must be an abstract continuous transition between regions A and B
      if there is a concrete continuous transition between a point in A
      and a point in B"

    but rather:

      "if there is a concrete continuous transition between points P and Q,
      then from any region that includes P there must be an abstract continuous
      transition to a region that includes Q".

    The former implies the latter, so the latter is weaker (and therefore makes
    for a better interface). In particular, the former does not let us avoid "drift",
    which we now describe.

    Suppose our concrete continuous state space is CR, and our regions
    are intervals of the form [n,n+1] with n a nat. And suppose that for some
    location l the corresponding concrete flow function is nondecreasing.

    Now consider the matter of whether there should/will be an abstract
    continuous transition from [1,2] to [0,1]. Clearly, we don't want this
    transition, because it would essentially introduce leftward abstract flow
    while the concrete flow is rightward (with devastating consequences for
    provability of safety).

    However, the traditional condition mentioned above /would/ demand such
    an abstract transition, because in the concrete system, there is a continuous
    transition from 1 (a point in the source region) to 1 (a point in the target
    region), namely with duration zero.

    Our more subtle condition, on the other hand, does not demand this abstract
    transition. It permits the omission of [0,1] from the list of regions computed
    given [1,2] as source region, as long as all points one can flow to (including
    1) are covered by /some/ region in the list. In this case, since [1,2] covers 1,
    and 1 is the only point in [0,1] one can flow to from [1,2], including [1,2] in
    the list removes the need to include [0,1].

    Note that the specification of this condition only ensures that the solution
    described /can/ work. Actually constructing a "smart" abstract continuous
    transition function which takes care to pick the "right" regions for its result
    list is a different matter, treated in hinted_abstract_continuous_transitions.v.
  *)

  Definition DiscRespect (s: State ap) (l: list (State ap)): Prop :=
      forall p1 (s2 : concrete.State chs),
        concrete.disc_trans (fst s, p1) s2 ->
        in_region ap p1 (snd s) ->
         DN (exists r2, in_region ap (concrete.point s2) r2 /\ In (concrete.location s2, r2) l).

  (* We define abstract versions of initiality, invariance, and guards, suitable
   as overestimation predicates. *)

  Definition Initial (s: State ap): Prop :=
    exists p, in_region ap p (snd s) /\ concrete.initial (fst s, p).

  Definition invariant (ls: State ap): Prop :=
    exists p, in_region ap p (snd ls) /\
      concrete.invariant (fst ls, p).

  Definition guard (l: concrete.Location chs) (s: Region ap) (l': concrete.Location chs): Prop
    := exists p, in_region ap p s /\
	concrete.guard chs (l, p) l'.

  Record System: Type :=
    { initial_dec: overestimator Initial
    ; disc_trans: forall s: State ap,
      sig (fun l: list (State ap) => LazyProp (NoDup l /\ DiscRespect s l))
    ; cont_trans: forall s: State ap,
      sig (fun l: list (Region ap) => LazyProp (NoDup l /\ ContRespect s l))
    }.

  Variable ahs: System.

  Let c_State := concrete.State chs.

  Definition abs (s: c_State) (s': State ap): Prop :=
    concrete.location s = fst s' /\
    in_region ap (snd s) (snd s').
  Hint Unfold abs.

  Definition trans (b : bool) (s1 s2 : State ap) : Prop :=
    let (l1, p1) := s1 in
    let (l2, p2) := s2 in
      if b then
        l1 = l2 /\ In p2 (proj1_sig (cont_trans ahs s1))
      else
        In s2 (proj1_sig (disc_trans ahs s1)).

  Definition reachable (s : State ap) : Prop :=
    exists is: State ap,
      overestimation_bool (initial_dec ahs is) = true /\ reachable_alternating trans is s.

  Hint Unfold Initial.

  Lemma reachable_alternating_concrete_abstract (i s: c_State):
    concrete.initial i -> forall b, end_with
      (fun b => if b then @concrete.disc_trans chs else @concrete.cont_trans chs) b i s ->
      DN (exists is s',
       overestimation_bool (initial_dec ahs is) = true /\
       abs s s' /\
       end_with trans (negb b) is s').
  Proof with eauto.
    intros i s H b H0.
    induction H0 as [| b i (l, p) H0 IH [l' p']].
      destruct s as [l cp].
      apply (DN_fmap (regions_cover ap l cp (concrete.invariant_initial chs _ H))).
      intro.
      destruct H0.
      exists (l, x).
      exists (l, x).
      split...
      apply overestimation_true...
    apply IH in H.
    clear IH.
    apply (DN_bind H).
    intros [ir [[al r] [H2 [[H3 H5] H4]]]].
    apply (@DN_exists (State ap) (fun is => exists s',
     overestimation_bool (initial_dec ahs is) = true /\
     abs (l', p') s' /\ end_with trans (negb b) is s') ir).
    pose proof (end_with_next (negb b) H4). clear H4.
    simpl in H3.
    subst.
    cut (
      overestimation_bool (initial_dec ahs ir) = true /\
      DN (exists s' : State ap, abs (l', p') s' /\ end_with trans (negb b) ir s')).
      intros.
      destruct H3.
      apply (DN_fmap H4).
      intro.
      destruct H7.
      destruct H7.
      eauto.
    split...
    cut (DN (exists r0, in_region ap p' r0 /\ trans (negb b) (al, r) (l', r0))).
      intro.
      apply (DN_fmap H3).
      intros [x H9].
      exists (l', x).
      intuition.
    destruct b; simpl in H0 |- *.
      destruct (disc_trans ahs (al, r)).
      simpl.
      destruct l...
      apply (DN_bind (H4 p (l', p') H1 H5)).
      intro.
      destruct H7.
      destruct H7.
      apply DN_return...
    destruct (cont_trans ahs (al, r)).
    simpl.
    destruct l...
    destruct H1.
    apply (DN_bind (H4 p H5 _ H7)).
    intro.
    destruct H8.
    destruct H8.
    apply DN_return.
    exists x0.
    intuition.
  Qed. (* todo: clean up proof *)

  Lemma reachable_concrete_abstract (s : concrete.State chs) :
    concrete.reachable s -> DN (exists s', abs s s' /\ reachable s').
  Proof.
    intros.
    destruct (concrete.alternating_reachable H) as [s' [H0 [x0 H1]]].
    unfold reachable.
    apply (DN_fmap (@reachable_alternating_concrete_abstract s' s H0 x0 H1)).
    intros [x [y [A [B C]]]].
    eauto 10.
  Qed.

  Lemma safe (s : concrete.State chs) :
    (forall s', abs s s' -> ~ reachable s') -> ~ concrete.reachable s.
  Proof.
    intros s H H0.
    apply (DN_apply (reachable_concrete_abstract H0) _ Stable_False).
    intros [s' [H1 H2]].
    apply (H s'); assumption.
  Qed.

End contents.

Existing Instance Region_eq_dec.
Existing Instance regions.
Existing Instance in_region_mor.
