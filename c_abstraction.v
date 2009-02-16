Require Import List.
Require Import util.
Require Import c_util.
Require Import CSetoids.
Require Import CRreal.
Require Import c_flow.
Require c_concrete.
Require abstract.
Require c_respect.
Set Implicit Arguments.
Open Local Scope CR_scope.

Section contents.

  Definition weak_decider T (P: T -> Prop) :=
    forall x, option (~ P x).

  (* Suppose we wish to abstract a concrete system.. *)

  Variable conc_sys: c_concrete.System.

  Let Location := c_concrete.Location conc_sys.
  Let Point := c_concrete.Point conc_sys.
    (* convenience *)

  (* We will need decideable equality on the system's locations, as
   well as a set of regions (which can contain Points), and
   exhaustive lists of locations and regions. *)

  Variables
    (Region: Set) (Region_eq_dec: forall i i': Region, decision (i=i'))
    (in_region: c_concrete.Point conc_sys -> Region -> Prop)
    (select_region: Point -> Region)
      (* select_region does not have to be constructive, because it is only
       used in the correctness proof. *)
    (regions: list Region) (regions_complete: forall i, List.In i regions).

  (* We can now define the abstract states: *)

  Let State: Set := prod Location Region.

  Definition State_eq_dec (s s': State): decision (s=s').
    unfold State.
    apply (pair_eq_dec (c_concrete.Location_eq_dec conc_sys) Region_eq_dec).
  Defined.

  Definition states: list State :=
    flat_map (fun l => map (pair l) regions) (c_concrete.locations conc_sys).

  Lemma states_complete: forall s, List.In s states.
  Proof with auto.
    destruct s.
    unfold states.
    destruct (in_flat_map (fun l => map (pair l) regions)
      (c_concrete.locations conc_sys) (l, r)).
    apply H0.
    exists l.
    split.
      apply c_concrete.locations_exhaustive.
    apply in_map...
  Qed.

  (* Next, we define the "ideal" criteria for when there should be
   transitions between abstract states, as well as for when
   an abstract state should be initial. *)

  Definition initial_condition (l: State): Prop :=
    exists p, in_region p (snd l) /\
    c_concrete.initial (fst l, p).

  Definition cont_trans_cond
    (l: prod Location (prod Region Region)): Prop :=
    exists p, exists q,
      in_region p (fst (snd l)) /\ in_region q (snd (snd l)) /\
      c_concrete.cont_trans (fst l, p) (fst l, q).

  Definition disc_trans_cond (l: prod State State): Prop :=
    exists p, exists q,
      in_region p (snd (fst l)) /\ in_region q (snd (snd l)) /\
      c_concrete.disc_trans (fst (fst l), p) (fst (snd l), q).

  Variables
    (cont_decider: weak_decider cont_trans_cond)
    (disc_decider: weak_decider disc_trans_cond)
    (initial_decider: weak_decider initial_condition).

  (* Using these, we can define the abstract transitions.. *)

  Let cont_trans_b (l: Location) (s s': Region): bool :=
    negb (opt_to_bool (cont_decider (l, (s, s')))).
  Let disc_trans_b (s s': State): bool :=
    negb (opt_to_bool (disc_decider (s, s'))).

  Definition cont_trans (s: State): list State :=
    map (pair (fst s)) (filter (cont_trans_b (fst s) (snd s)) regions).
  Definition disc_trans (s: State): list State :=
    filter (disc_trans_b s) states.
      (* a more efficient implementation would grow the graph *)

  Definition initial (s: State): bool := negb (opt_to_bool (initial_decider s)).

  (* .. and the abstract system itself: *)

  Definition abs_sys: abstract.System :=
    abstract.Build_System State_eq_dec states states_complete initial cont_trans disc_trans.

  (* Next, we will show that this abstract system respects the concrete
   system by the following abstraction function: *)

  Definition abs (s: c_concrete.State conc_sys): abstract.State abs_sys :=
    match s with
    | pair l p => pair l (select_region p)
    end.

  Lemma fst_abs s: fst (abs s) = fst s.
  Proof. destruct s. reflexivity. Qed.

  Definition RegionsCoverInvariants: Prop :=
    forall l p, c_concrete.invariant (l, p) ->
      in_region p (select_region p).

  Hypothesis regions_cover_invariants: RegionsCoverInvariants.

  Lemma respects_initial
    (s: c_concrete.Location conc_sys * c_concrete.Point conc_sys):
    c_concrete.initial s -> abstract.initial (abs s) = true.
  Proof with auto.
    intros. destruct s. unfold abs. simpl. unfold initial.
    destruct (initial_decider (l, select_region c))...
    elimtype False. apply n. clear n.
    unfold initial_condition.
    exists c. split... simpl snd.
    apply regions_cover_invariants with l.
    apply c_concrete.invariant_initial...
  Qed.

  Lemma respects_disc (s1 s2: c_concrete.State conc_sys):
    c_concrete.disc_trans s1 s2 -> In (abs s2) (abstract.disc_trans (abs s1)).
  Proof with auto.
    intros.
    unfold abstract.disc_trans, abs_sys, disc_trans.
    destruct (filter_In (disc_trans_b (abs s1)) (abs s2) states).
    apply H1.
    split. apply states_complete.
    unfold disc_trans_b.
    destruct (disc_decider (@pair State State (abs s1) (abs s2)))...
    elimtype False.
    apply n. clear n H0 H1.
    unfold disc_trans_cond.
    simpl fst. simpl snd.
    destruct H. destruct H0. destruct H1.
    exists (snd s1). exists (snd s2).
    repeat rewrite fst_absFunc.
    simpl c_concrete.Location. simpl c_concrete.Point.
    destruct s1. destruct s2.
    split. apply regions_cover_invariants with l...
    split. apply regions_cover_invariants with l0...
    unfold c_concrete.disc_trans...
  Qed.

  Add Morphism (c_concrete.inv_curried conc_sys)
    with signature (@eq _) ==> (@cs_eq _) ==> iff
    as inv_mor.
  Proof.
    intros.
    apply c_concrete.invariant_wd.
      reflexivity.
    assumption.
  Qed.

  Lemma respects_cont s1 s2: (c_concrete.cont_trans s1 s2) ->
    In (abs s2) (abstract.cont_trans (abs s1)).
  Proof with auto with real.
    unfold abs_sys, c_concrete.cont_trans. simpl abstract.cont_trans.
    intros. destruct s1. destruct s2.
    unfold cont_trans.
    destruct H. destruct H0. destruct H0. simpl in * |-. subst.
    rewrite fst_abs.
    simpl fst.
    rename l0 into l.
    simpl abs.
    apply in_map.
    simpl fst. simpl snd.
    destruct (filter_In
      (cont_trans_b l (select_region c)) (select_region c0) regions).
    apply H2. clear H2 H.
    split. apply regions_complete.
    unfold cont_trans_b.
    destruct (cont_decider (@pair Location (prod Region Region) l
      (@pair Region Region (select_region c) (select_region c0))))...
    elimtype False. apply n. clear n.
    unfold cont_trans_cond.
    simpl fst. simpl snd.
    exists c. exists c0.
    split.
      apply regions_cover_invariants with l.
      rewrite c_concrete.curry_inv.
      rewrite <- (flow_zero (c_concrete.flow conc_sys l) c).
      apply H0.
        apply CRle_refl.
      destruct x... simpl.
      apply (CRnonNeg_le_zero x)...
    split.
      apply regions_cover_invariants with l.
      rewrite c_concrete.curry_inv.
      rewrite <- H1.
      apply H0.
        destruct x... simpl. apply (CRnonNeg_le_zero x)...
      apply CRle_refl.
    unfold c_concrete.cont_trans.
    simpl.
    split...
    exists x...
  Qed.

  (* Et voila: *)

  Theorem respect: c_respect.Respects abs_sys abs.
  Proof c_respect.Build_Respects abs_sys abs
   respects_initial respects_disc respects_cont.

  Definition result:
    { abs_sys: abstract.System &
    { abs: c_concrete.State conc_sys -> abstract.State abs_sys
    | c_respect.Respects abs_sys abs } }.
  Proof. exists abs_sys. exists abs. apply respect. Defined.

End contents.
