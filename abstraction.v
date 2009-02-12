Require Import List.
Require Import util.
Require concrete.
Require abstract.
Set Implicit Arguments.

Section contents.

  (* Suppose we wish to abstract a concrete system.. *)

  Variable concrete_system: concrete.System.

  Let Location := concrete.Location concrete_system.
  Let Point := concrete.Point concrete_system.
    (* convenience *)

  (* We will need decideable equality on the system's locations, as
   well as a set of regions (which can contain Points), and
   exhaustive lists of locations and regions. *)

  Variables
    (Location_eq_dec: forall l l': Location, decision (l=l'))
    (Region: Set) (Region_eq_dec: forall i i': Region, decision (i=i'))
    (in_region: concrete.Point concrete_system -> Region -> Prop)
    (select_region: Point -> Region)
    (locations: list Location) (locations_complete: forall l, List.In l locations)
    (regions: list Region) (regions_complete: forall i, List.In i regions).

  (* We can now define the abstract states: *)

  Let State: Set := prod Location Region.

  Definition State_eq_dec (s s': State): decision (s=s').
    unfold State.
    apply (pair_eq_dec Location_eq_dec Region_eq_dec).
  Defined.

  Definition states: list State :=
    flat_map (fun l => map (pair l) regions) locations.

  Lemma states_complete: forall s, List.In s states.
  Proof with auto.
    destruct s.
    unfold states.
    destruct (in_flat_map (fun l => map (pair l) regions) locations (l, r)).
    apply H0.
    exists l.
    split...
    apply in_map...
  Qed.

  (* Next, we define the "ideal" criteria for when there should be
   transitions between abstract states, as well as for when
   an abstract state should be initial. *)

  Definition initial_condition (l: State): Prop :=
    exists p, in_region p (snd l) /\
    concrete.initial concrete_system (fst l, p).

  Definition continuous_transition_condition
    (l: prod Location (prod Region Region)): Prop :=
    exists p, exists q,
      in_region p (fst (snd l)) /\ in_region q (snd (snd l)) /\
      concrete.cont_trans (fst l, p) (fst l, q).

  Definition discrete_transition_condition
    (l: prod State State): Prop :=
    exists p, exists q,
      in_region p (snd (fst l)) /\ in_region q (snd (snd l)) /\
      concrete.disc_trans (fst (fst l), p) (fst (snd l), q).

  (* These are not decideable, however, so we'll let users specify
   weak deciders for these conditions. *)

  Variables
    (cont_decider: decideable_overestimator continuous_transition_condition)
    (disc_decider: decideable_overestimator discrete_transition_condition)
    (initial_decider: decideable_overestimator initial_condition).

  (* Using these, we can define the abstract transitions.. *)

  Definition canContTrans (l: Location) (s s': Region): bool :=
    unsumbool (doe_dec cont_decider (l, (s, s'))).
  Definition canDiscTrans (s s': State): bool :=
    unsumbool (doe_dec disc_decider (s, s')).

  Definition contTrans (s: State): list State :=
    map (pair (fst s)) (filter (canContTrans (fst s) (snd s)) regions).
  Definition discreteTrans (s: State): list State :=
    filter (canDiscTrans s) states.
      (* a more efficient implementation would grow the graph *)

  Definition initial (s: State): bool :=
    unsumbool (doe_dec initial_decider s).

  (* .. and the abstract system itself: *)

  Definition abstract_system: abstract.System :=
    abstract.Build_System State_eq_dec initial contTrans discreteTrans.

  (* Next, we will show that this abstract system respects the concrete
   system by the following abstraction function: *)

  Definition absFunc (s: concrete.State concrete_system): State :=
    match s with
    | pair l p => pair l (select_region p)
    end.

  Lemma fst_absFunc s: fst (absFunc s) = fst s.
  Proof. destruct s. reflexivity. Qed.

  Hypothesis regions_cover_invariants: forall l p,
    concrete.invariant concrete_system (l, p) ->
    in_region p (select_region p).

  Lemma respectsInit
    (s: concrete.Location concrete_system * concrete.Point concrete_system):
    concrete.initial concrete_system s ->
    abstract.initial abstract_system (absFunc s) = true.
  Proof with auto.
    intros.
    destruct s.
    unfold absFunc.
    simpl.
    unfold initial.
    destruct (doe_dec initial_decider (l, select_region p))...
    elimtype False. apply n. clear n.
    apply doe_correct.
    unfold initial_condition.
    exists p.
    split...
    simpl snd.
    apply regions_cover_invariants with l.
    apply concrete.invariant_initial...
  Qed.

  Lemma respectsDisc (s1 s2: concrete.State concrete_system):
    concrete.disc_trans s1 s2 ->
    In (absFunc s2) (abstract.disc_trans abstract_system (absFunc s1)).
  Proof with auto.
    intros.
    unfold abstract.disc_trans, abstract_system, discreteTrans.
    destruct (filter_In (canDiscTrans (absFunc s1)) (absFunc s2) states).
    apply H1.
    split.
      apply states_complete.
    unfold canDiscTrans.
    destruct (doe_dec disc_decider (absFunc s1, absFunc s2))...
    elimtype False.
    apply n.
    clear n H0 H1.
    apply doe_correct.
    unfold discrete_transition_condition.
    simpl fst. simpl snd.
    destruct H.
    destruct H0.
    destruct H1.
    exists (snd s1).
    exists (snd s2).
    simpl snd.
    repeat rewrite fst_absFunc.
    simpl in H0.
    simpl concrete.Location. simpl concrete.Point.
    split.
      destruct s1. simpl.
      apply regions_cover_invariants with l...
    split.
      destruct s2. simpl.
      apply regions_cover_invariants with l...
    unfold concrete.disc_trans.
    simpl fst. simpl snd.
    destruct s1.
    split...
    split...
    split...
    destruct s2...
  Qed.

  Lemma respectsCont s1 s2: (concrete.cont_trans s1 s2) ->
    In (absFunc s2) (abstract.cont_trans abstract_system (absFunc s1)).
  Proof with auto with real.
    intros.
    unfold abstract_system.
    simpl abstract.cont_trans.
    destruct s1. destruct s2.
    unfold concrete.cont_trans in H.
    unfold contTrans.
    destruct H. destruct H0. destruct H0. simpl in * |-. subst.
    rewrite fst_absFunc.
    simpl fst.
    rename l0 into l.
    simpl absFunc.
    apply in_map.
    simpl fst. simpl snd.
    destruct (filter_In
      (canContTrans l (select_region p)) (select_region (concrete.flow concrete_system l p (proj1_sig x))) regions).
    clear H. apply H1. clear H1.
    split.
      apply regions_complete.
    unfold canContTrans.
    set (@doe_dec (prod Location (prod Region Region))
        continuous_transition_condition cont_decider
        (@pair Location (prod Region Region) l
           (@pair Region Region (select_region p)
              (select_region (concrete.flow concrete_system l p (proj1_sig x)))))).
    simpl.
    destruct d...
    elimtype False. apply n. clear n.
    apply doe_correct.
    unfold continuous_transition_condition.
    simpl fst. simpl snd.
    exists p. exists (concrete.flow concrete_system l p (proj1_sig x)).
    split.
      apply regions_cover_invariants with l.
      rewrite <- (concrete.flow_zero (concrete.flow_flows concrete_system l)) with p.
      destruct x...
    split.
      apply regions_cover_invariants with l.
      destruct x...
    unfold concrete.cont_trans.
    simpl fst. simpl snd.
    split...
    exists x...
  Qed.

  (* Et voila: *)

  Theorem respect: abstract.Respects abstract_system absFunc.
  Proof abstract.Build_Respects abstract_system absFunc respectsInit respectsDisc respectsCont.

  Lemma result:
    { abstract_system: abstract.System &
    { f: concrete.State concrete_system -> abstract.State abstract_system
    | abstract.Respects abstract_system f } }.
  Proof.
    exists abstract_system.
    exists absFunc.
    apply respect.
  Defined.

End contents.
