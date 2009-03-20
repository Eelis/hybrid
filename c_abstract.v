Require Import reachability.
Require Import List.
Require Import dec_overestimator.
Require Import list_util.
Set Implicit Arguments.
Require c_concrete.

Section contents.

  Variable chs: c_concrete.System.

  Section pre.

    Variables
      (Region : Set)
      (regions : list Region)
      (Region_eq_dec : forall r r': Region, decision (r=r'))
      (regions_exhaustive : forall r, In r regions)
      (NoDup_regions : NoDup regions).
    
    Definition State := (c_concrete.Location chs * Region)%type.

    Definition State_eq_dec (s s' : State) : decision (s = s').
    Proof.
      dec_eq. apply Region_eq_dec. apply c_concrete.Location_eq_dec.
    Defined.

    Definition states : list State :=
      flat_map (fun l => map (pair l) regions) (c_concrete.locations chs).

    Lemma states_exhaustive s : List.In s states.
    Proof with auto.
      destruct s.
      unfold states.
      destruct (in_flat_map (fun l => map (pair l) regions)
        (c_concrete.locations chs) (l, r)).
      apply H0. exists l. split. apply c_concrete.locations_exhaustive.
      apply in_map. apply regions_exhaustive.
    Qed.

    Lemma NoDup_states : NoDup states.
    Proof with auto.
      apply NoDup_flat_map; intros.
          destruct (fst (in_map_iff (pair a) regions x) H1).
          destruct (fst (in_map_iff (pair b) regions x) H2).
          destruct H3. destruct H4.
          subst. inversion H4...
        apply NoDup_map...
        intros. inversion H2...
      apply c_concrete.NoDup_locations.
    Qed.

  End pre.

  Record System: Type :=
    { Region: Set
    ; Region_eq_dec: forall r r': Region, decision (r=r')
    ; regions: list Region
    ; regions_exhaustive: forall r, In r regions
    ; NoDup_regions: NoDup regions
    ; select_region: c_concrete.Point chs -> Region
    ; initial_dec: State Region -> bool
    ; initial_pred : initial_dec >=> (fun s : State Region =>
      let (l, r) := s in
        exists p, select_region p = r /\ c_concrete.initial (l, p))
    ; disc_trans: State Region -> list (State Region)
    ; NoDup_disc_trans: forall s, NoDup (disc_trans s)
    ; disc_resp: forall s1 s2 : c_concrete.State chs,
        let (l1, p1) := s1 in
        let (l2, p2) := s2 in
          c_concrete.disc_trans s1 s2 ->
          In (l2, select_region p2) (disc_trans (l1, select_region p1))
    ; cont_trans: State Region -> list Region
    ; NoDup_cont_trans: forall s, NoDup (cont_trans s)
    ; cont_resp: forall l s1 s2,
        c_concrete.cont_trans' chs l s1 s2 ->
        In (select_region s2) (cont_trans (l, select_region s1))
    }.

  Variable ahs: System.

  Let State := State (Region ahs).
  Let c_State := c_concrete.State chs.

  Definition abs (s : c_State) : State :=
    let (l, p) := s in
      (l, select_region ahs p).

  Definition trans (b : bool) (s1 s2 : State) : Prop :=
    let (l1, p1) := s1 in
    let (l2, p2) := s2 in
      if b then
        l1 = l2 /\ In p2 (cont_trans _ s1)
      else
        In s2 (disc_trans _ s1).

  Definition reachable (s : State) : Prop :=
    exists is : State, 
      initial_dec ahs is = true /\ reachable_alternating trans is s.

  Lemma reachable_alternating_concrete_abstract (s : c_concrete.State chs) :
    c_concrete.reachable_alternating s -> reachable (abs s).
  Proof with auto.
    intros. destruct H as [is [is_init ra]]. exists (abs is).
    simpl. split.
    change (do_pred (mk_DO (initial_pred ahs)) (abs is) = true).
    apply do_over_true. destruct is as [il ip]. exists ip...
    destruct ra as [b trace]. exists (negb b). 
    induction trace. 
    apply end_with_refl.
    apply end_with_next with (abs y)...
    set (dr := disc_resp ahs y z).
    destruct y. destruct z. destruct b. unfold trans; simpl.
    apply dr...
    split.
    destruct H...
    apply cont_resp. destruct H...
  Qed.

  Lemma reachable_concrete_abstract (s : c_concrete.State chs) :
    c_concrete.reachable s -> reachable (abs s).
  Proof.
    intros. apply reachable_alternating_concrete_abstract.
    apply c_concrete.alternating_reachable. hyp.
  Qed.

End contents.

Implicit Arguments initial_dec [s].
Implicit Arguments cont_trans [s].
Implicit Arguments disc_trans [s].
