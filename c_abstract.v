Require Import reachability.
Require Import List.
Require Import util.
Require Import list_util.
Set Implicit Arguments.
Require c_concrete.

Section contents.

  Variable chs: c_concrete.System.

  Section pre.

    Variables
      (Region: Set)
      (regions: list Region)
      (Region_eq_dec: forall r r': Region, decision (r=r'))
      (regions_exhaustive: forall r, In r regions)
      (NoDup_regions: NoDup regions).
    
    Definition State := (c_concrete.Location chs * Region)%type.

    Definition State_eq_dec (s s': State): decision (s=s').
      unfold State.
      apply (pair_eq_dec (c_concrete.Location_eq_dec chs) Region_eq_dec).
    Defined.

    Definition states: list State :=
      flat_map (fun l => map (pair l) regions) (c_concrete.locations chs).

    Lemma states_exhaustive: forall s, List.In s states.
    Proof with auto.
      destruct s.
      unfold states.
      destruct (in_flat_map (fun l => map (pair l) regions)
        (c_concrete.locations chs) (l, r)).
      apply H0.
      exists l.
      split.
        apply c_concrete.locations_exhaustive.
      apply in_map.
      apply regions_exhaustive.
    Defined.

    Lemma NoDup_states: NoDup states.
    Proof with auto.
      unfold states.
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
    ; initial: forall (l: c_concrete.Location chs) (r: Region),
        option (forall p, select_region p = r -> ~ c_concrete.initial (l, p))

    ; disc_trans: forall (l: c_concrete.Location chs) (r: Region),
	{ r': list (c_concrete.Location chs * Region) |
           forall p s, select_region p = r ->
            c_concrete.disc_trans (l, p) s ->
            In (fst s, select_region (snd s)) r' }
    ; NoDup_disc_trans: forall l r, NoDup (proj1_sig (disc_trans l r))

    ; cont_trans: forall (l: c_concrete.Location chs) (r: Region),
        { r': list Region | forall p q, select_region p = r ->
            c_concrete.cont_trans' _ l p q -> In (select_region q) r' }
    ; NoDup_cont_trans: forall l r, NoDup (proj1_sig (cont_trans l r))
    }.

  Variable ahs: System.

  Let State := State (Region ahs).

  Definition abs (p: c_concrete.State chs): State :=
    (fst p, select_region ahs (snd p)).

  Definition trans (b: bool) (s s': State): Prop :=
    if b
      then fst s = fst s' /\ In (snd s') (proj1_sig (cont_trans _ (fst s) (snd s)))
      else In s' (proj1_sig (disc_trans _ (fst s) (snd s))).
      
  Definition reachable (s: State): Prop :=
    exists i, opt_to_bool (initial ahs (fst i) (snd i)) = false /\
      reachable_alternating trans i s.

  Lemma reachable_alternating_concrete_abstract (s: c_concrete.State chs):
    c_concrete.reachable_alternating s -> reachable (abs s).
  Proof with auto.
    unfold c_concrete.reachable_alternating.
    intros. destruct H. destruct H. exists (abs x).
    split...
      unfold abs.
      simpl.
      destruct (initial ahs (fst x) (select_region ahs (snd x)))...
      destruct x.
      elimtype False. apply (n _ (refl_equal _) H).
    destruct H0.
    exists (negb x0).
    induction H0. apply end_with_refl.
    apply end_with_next with (abs y)...
    unfold trans.
    destruct b; simpl.
      destruct (disc_trans ahs (fst y) (select_region ahs (snd y))).
      simpl.
      unfold abs.
      apply i with (snd y)...
      destruct y...
    split.
      unfold c_concrete.cont_trans in H1. destruct H1...
    destruct (cont_trans ahs (fst y) (select_region ahs (snd y))).
    simpl.
    apply i with (snd y)...
    destruct H1...
  Defined.

  Lemma reachable_concrete_abstract (s: c_concrete.State chs):
    c_concrete.reachable s -> reachable (abs s).
  Proof.
    intros. apply reachable_alternating_concrete_abstract.
    apply c_concrete.alternating_reachable. assumption.
  Defined.

End contents.

Implicit Arguments initial [s].
Implicit Arguments cont_trans [s].
Implicit Arguments disc_trans [s].

