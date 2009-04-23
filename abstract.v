Require Import reachability.
Require Import List.
Require Import dec_overestimator.
Require Import list_util.
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
    ; select_region: concrete.Point chs -> Region
    ; initial_dec: State Region -> bool
    ; initial_pred : initial_dec >=> (fun s : State Region =>
      let (l, r) := s in
        exists p, select_region p = r /\ concrete.initial (l, p))
    ; disc_trans: State Region -> list (State Region)
    ; NoDup_disc_trans: forall s, NoDup (disc_trans s)
    ; disc_resp: forall s1 s2 : concrete.State chs,
        let (l1, p1) := s1 in
        let (l2, p2) := s2 in
          concrete.disc_trans s1 s2 ->
          In (l2, select_region p2) (disc_trans (l1, select_region p1))
    ; cont_trans: State Region -> list Region
    ; NoDup_cont_trans: forall s, NoDup (cont_trans s)
    ; cont_resp: forall l s1 s2,
        concrete.cont_trans' chs l s1 s2 ->
        In (select_region s2) (cont_trans (l, select_region s1))
    }.

  Variable ahs: System.

  Let State := State (Region ahs).
  Let c_State := concrete.State chs.

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

  Lemma reachable_alternating_concrete_abstract (s : concrete.State chs) :
    concrete.reachable_alternating s -> reachable (abs s).
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

  Lemma reachable_concrete_abstract (s : concrete.State chs) :
    concrete.reachable s -> reachable (abs s).
  Proof.
    intros. apply reachable_alternating_concrete_abstract.
    apply concrete.alternating_reachable. hyp.
  Qed.

End contents.

Hint Resolve Region_eq_dec regions: typeclass_instances.
Implicit Arguments State [].
Implicit Arguments initial_dec [s].
Implicit Arguments cont_trans [s].
Implicit Arguments disc_trans [s].
