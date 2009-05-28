Require Import reachability.
Require Import List Bool.
Require Import util list_util.
Set Implicit Arguments.
Require EquivDec.
Require concrete.

Section contents.

  Variable chs: concrete.System.

  Section pre.

    Context {Region: Set}.

    Definition State := (concrete.Location chs * Region)%type.

    Context
      {Region_eq_dec: EquivDec.EqDec Region eq}
      {regions: ExhaustiveList Region}.

    Hypothesis NoDup_regions: NoDup regions.

    Definition states := @ExhaustivePairList (concrete.Location chs) Region _ _.

    Lemma NoDup_states : NoDup states.
    Proof with auto.
      unfold exhaustive_list. simpl.
      apply NoDup_flat_map; intros.
          destruct (fst (in_map_iff (pair a) regions x) H1).
          destruct (fst (in_map_iff (pair b) regions x) H2).
          destruct H3. destruct H4.
          subst. inversion H4...
        apply NoDup_map...
        intros. inversion H2...
      apply concrete.NoDup_locations.
    Qed.

  End pre.

  Implicit Arguments State [].

  Record System: Type :=
    { Region: Set
    ; Region_eq_dec: EquivDec.EqDec Region eq
    ; regions: ExhaustiveList Region
    ; NoDup_regions: NoDup regions
    ; in_region: concrete.Point chs -> Region -> Prop
    ; select_region: forall l p, concrete.invariant (l, p) -> exists r, in_region p r
    ; Initial: State Region -> Prop
      := fun s => exists p, in_region p (snd s) /\ concrete.initial (fst s, p)
    ; initial_dec: forall s, overestimation (Initial s)
    ; disc_trans: State Region -> list (State Region)
    ; NoDup_disc_trans: forall s, NoDup (disc_trans s)
    ; disc_resp: forall s1 s2 : concrete.State chs,
        let (l1, p1) := s1 in
        let (l2, p2) := s2 in
          concrete.disc_trans s1 s2 ->
          forall r1, in_region p1 r1 ->
            exists r2, in_region p2 r2 /\ In (l2, r2) (disc_trans (l1, r1))
    ; cont_trans: State Region -> list Region
    ; NoDup_cont_trans: forall s, NoDup (cont_trans s)
    ; cont_resp: forall l s1 s2,
        concrete.cont_trans' chs l s1 s2 ->
        forall r1, in_region s1 r1 ->
          exists r2, in_region s2 r2 /\ In r2 (cont_trans (l, r1))
    }.

  (* Note that the definition of cont_resp below is no longer the traditional
      "there is an abstract continuous transition between regions A and B
      if there is a concrete continuous transition between a point in A
      and a point in B"
   but rather:
      "if there is a concrete continuous transition between points P and Q,
      then from any region that includes P there is an abstract continuous
      transition to a region that includes Q".
   The former implies the latter, so the latter is weaker (and therefore better).
   In particular, the former does not let us avoid drift, while the latter does. *)

  Variable ahs: System.

  Let State := State (Region ahs).
  Let c_State := concrete.State chs.

  Definition abs (s: c_State) (s': State): Prop :=
    fst s = fst s' /\ in_region ahs (snd s) (snd s').
  Hint Unfold abs.

  Definition trans (b : bool) (s1 s2 : State) : Prop :=
    let (l1, p1) := s1 in
    let (l2, p2) := s2 in
      if b then
        l1 = l2 /\ In p2 (cont_trans _ s1)
      else
        In s2 (disc_trans _ s1).

  Definition reachable (s : State) : Prop :=
    exists is : State, 
      (initial_dec ahs is: bool) = true /\ reachable_alternating trans is s.

  Hint Unfold Initial.

  Lemma reachable_alternating_concrete_abstract (i s: c_State):
    concrete.initial i -> forall b, end_with
      (fun b => if b then @concrete.disc_trans chs else @concrete.cont_trans chs) b i s ->
   (exists is, (initial_dec ahs is: bool) = true /\ exists s', abs s s' /\ end_with trans (negb b) is s').
  Proof with eauto.
    intros i s H b H0.
    induction H0.
      destruct s as [l cp].
      destruct (select_region ahs l cp).
        apply (concrete.invariant_initial chs _ H).
      exists (l, x).
      split.
        destruct (initial_dec ahs (l, x)). simpl.
        destruct x0... elimtype False. apply n...
      exists (l, x)...
    intuition.
    destruct H2 as [x0 [H2 [x1 [H3 H4]]]].
    exists x0. split...
    rewrite negb_involutive in H4.
    destruct y.
    destruct H3.
    simpl in H3.
    subst.
    destruct x1 as [l0 r].
    destruct z as [l s0].
    destruct b.
      destruct (disc_resp ahs (l0, s) (l, s0) H1 _ H5) as [x2 [H3 H6]].
      exists (l, x2)...
    destruct H1.
    destruct (cont_resp ahs H3 r H5) as [x2 [H6 H7]].
    exists (l, x2).
    split...
    apply end_with_next with (l0, r)...
    simpl...
  Qed.

  Lemma reachable_concrete_abstract (s : concrete.State chs) :
    concrete.reachable s -> exists s', abs s s' /\ reachable s'.
  Proof.
    intros.
    destruct (concrete.alternating_reachable H) as [s' [H0 [x0 H1]]].
    unfold reachable.
    destruct (@reachable_alternating_concrete_abstract s' s H0 x0 H1) as [A [B [u [C D]]]].
    eauto 10.
  Qed.

  Lemma safe (s : concrete.State chs) :
    (forall s', abs s s' -> ~ reachable s') -> ~ concrete.reachable s.
  Proof.
    repeat intro.
    destruct (reachable_concrete_abstract H0) as [s' [H1 H2]].
    apply (H s' H1 H2).
  Qed.

End contents.

Hint Resolve Region_eq_dec regions: typeclass_instances.
Implicit Arguments State [].
Implicit Arguments initial_dec [s].
Implicit Arguments cont_trans [s].
Implicit Arguments disc_trans [s].
