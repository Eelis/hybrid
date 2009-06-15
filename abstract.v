Require Import reachability.
Require Import List Bool.
Require Import util list_util.
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
    ; select_region: forall l p, concrete.invariant (l, p) -> sig (in_region p)
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

    Program Let select_region l p (H: concrete.invariant (l, p)): sig (in_region p)
      := (select_region ap _ _ H, select_region ap' _ _ H).

    Next Obligation. split; simpl; destruct select_region; assumption. Qed.

    Definition param_prod: Parameters := Build_Parameters  _ _
      (NoDup_ExhaustivePairList (NoDup_regions ap) (NoDup_regions ap'))
      in_region_mor select_region.

  End param_prod.

  Variable ap: Parameters.

  Definition ContRespect (s: State ap) (l: list (Region ap)): Prop :=
     forall p, in_region ap p (region s) ->
     forall q, concrete.can_flow chs (location s) p q ->
       exists r', in_region ap q r' /\ In r' l.

  (* Note that this is no longer the traditional
      "there is an abstract continuous transition between regions A and B
      if there is a concrete continuous transition between a point in A
      and a point in B"
   but rather:
      "if there is a concrete continuous transition between points P and Q,
      then from any region that includes P there is an abstract continuous
      transition to a region that includes Q".
   The former implies the latter, so the latter is weaker (and therefore better).
   In particular, the former does not let us avoid drift, while the latter does. *)

  Definition DiscRespect (s: State ap) (l: list (State ap)): Prop :=
      forall p1 (s2 : concrete.State chs) ,
        concrete.disc_trans (fst s, p1) s2 ->
        in_region ap p1 (snd s) ->
         exists r2, in_region ap (concrete.point s2) r2 /\ In (concrete.location s2, r2) l.

  Definition Initial (s: State ap): Prop :=
    exists p, in_region ap p (snd s) /\ concrete.initial (fst s, p).

  Record System: Type :=
    { initial_dec: forall s, overestimation (Initial s)
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
      (initial_dec ahs is: bool) = true /\ reachable_alternating trans is s.

  Hint Unfold Initial.

  Lemma reachable_alternating_concrete_abstract (i s: c_State):
    concrete.initial i -> forall b, end_with
      (fun b => if b then @concrete.disc_trans chs else @concrete.cont_trans chs) b i s ->
   (exists is, (initial_dec ahs is: bool) = true /\ exists s', abs s s' /\ end_with trans (negb b) is s').
  Proof with eauto.
    intros i s H b H0.
    induction H0 as [| b i (l, p) H0 IH [l' p']].
      destruct s as [l cp].
      destruct (select_region ap l cp).
        apply (concrete.invariant_initial chs _ H).
      exists (l, x).
      split.
        apply overestimation_true...
      exists (l, x)...
    destruct IH as [ir [H2 [[al r] [[H3 H5] H4]]]]...
    exists ir. split...
    pose proof (end_with_next (negb b) H4). clear H4.
    simpl in H3.
    subst.
    cut (exists r0, in_region ap p' r0 /\ trans (negb b) (al, r) (l', r0)).
      intros [x H3].
      exists (l', x).
      intuition.
    destruct b; simpl in H0 |- *.
      destruct (disc_trans ahs (al, r)).
      simpl.
      destruct l...
      destruct (H4 p (l', p') H1 H5)...
    destruct (cont_trans ahs (al, r)).
    simpl.
    destruct l...
    destruct H1.
    destruct (H4 p H5 _ H7).
    exists x0.
    intuition.
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

Existing Instance Region_eq_dec.
Existing Instance regions.
Existing Instance in_region_mor.
