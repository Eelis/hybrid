Require Import util.
Require Import c_util.
Require Import reachability.
Require Import CRreal.
Require Export c_flow.
Set Implicit Arguments.
Open Local Scope CR_scope.
Require EquivDec.

(* We require CR because we use it for Time. 
 Todo: Take an arbitrary (C)Ring/(C)Field for Time, so that
 the classical development does not need a separate concrete module. *)

Record System: Type :=
  { Point: CSetoid

  ; Location: Set
  ; Location_eq_dec: EquivDec.EqDec Location eq
  ; locations: ExhaustiveList Location
  ; NoDup_locations: NoDup locations

  ; initial: (Location * Point) -> Prop
  ; invariant: (Location * Point) -> Prop
  ; invariant_initial: forall s, initial s -> invariant s
  ; invariant_wd: forall l l', l = l' -> forall p p', cs_eq p p' ->
      (invariant (l, p) <-> invariant (l', p'))

  ; flow: Location -> Flow Point

  ; guard : (Location * Point) -> Location -> Prop
  ; reset: Location -> Location -> Point -> Point
    (* this separation of guard and reset seems to cause a problem:
    the paper allows having different transitions from a given (l, x) to
    some (l', x'), because you can have different transitions. we only allow one! *)
  }.

Hint Resolve Location_eq_dec locations: typeclass_instances.
Implicit Arguments initial [s].
Implicit Arguments invariant [s].

Section transitions_and_reachability.

  Variable system: System.

  Definition State: Type := (Location system * Point system)%type.

  Definition cont_trans' l (p p': Point system) : Prop :=
    exists d:Duration,
      (forall t, '0 <= t -> t <= proj1_sig d ->
        invariant (l, flow system l p t))
      /\ flow system l p (proj1_sig d) [=] p'.

  Definition cont_trans (s s': State) : Prop :=
    fst s = fst s' /\ cont_trans' (fst s) (snd s) (snd s').

  Definition disc_trans (s s': State) : Prop :=
    guard system s (fst s') /\
     reset system (fst s) (fst s') (snd s) = snd s' /\
      invariant s /\ invariant s'.

  Definition trans (s s': State): Prop := disc_trans s s' \/ cont_trans s s'.

  Notation "s ->_C s'" := (cont_trans s s') (at level 70).
  Notation "s ->_D s'" := (disc_trans s s') (at level 70).
  Notation "s ->_T s'" := (trans s s') (at level 90).

  Definition inv_curried (l: Location system) (p: Point system): Prop :=
    invariant (l, p).

  Definition curry_inv l p: invariant (l, p) = inv_curried l p.
  Proof. reflexivity. Qed.

  Add Morphism inv_curried
    with signature (@eq _) ==> (@cs_eq _) ==> iff
    as inv_mor.
  Proof with auto.
    intros.
    unfold inv_curried.
    apply invariant_wd...
  Qed.

  Add Morphism (@bsm (Point system) CRasCSetoid (Point system))
    with signature (@eq _) ==> (@cs_eq _) ==> (@cs_eq _) ==> (@cs_eq _)
    as gh_mor.
  Proof with auto.
    intro.
    exact (@bsm_mor (Point system) CRasCSetoid (Point system) y y (refl_equal _)).
  Qed.

  Lemma cont_trans_refl s: invariant s -> s ->_C s.
  Proof with auto.
    intros. unfold cont_trans. destruct s.
    split...
    exists NonNegCR_zero.
    split.
      intros.
      assert (t [=] '0).
        destruct (CRle_def t ('0))...
      rewrite curry_inv.
      rewrite H2.
      rewrite flow_zero...
    apply flow_zero.
  Qed.

  Lemma cont_trans_trans s s' s'':
    (s ->_C s') -> (s' ->_C s'') -> (s ->_C s'').
  Proof with auto.
    unfold cont_trans.
    intros. destruct s. destruct s'. destruct s''.
    simpl in *.
    destruct H. destruct H1. destruct H1.
    destruct H0. destruct H3. destruct H3. subst.
    split...
    exists (NonNegCR_plus x x0).
    destruct x. destruct x0. simpl in *.
    split.
      intros.
      destruct (CR_lt_eq_dec t x).
        apply H1...
        rewrite s2.
        apply CRle_refl.
      destruct s2.
        apply H1...
        apply CRlt_le...
      rewrite curry_inv.
      rewrite (t11 x t).
      rewrite flow_additive.
      rewrite H2.
      apply H3.
        apply (CRnonNeg_le_zero (t-x)).
        apply CRpos_nonNeg...
      rewrite (t11 x x0).
      rewrite (Radd_assoc CR_ring_theory).
      apply (t2 (-x) H0).
    rewrite flow_additive.
    rewrite H2...
  Qed.

  Lemma cont_trans_preserves_location s s': s ->_C s' -> fst s = fst s'.
  Proof. intros. destruct H; auto... Qed.

  (* hm, the paper distinguishes between R^n and the
  subset that is the continuous state space for the HS, and i
  seem to recall that flowing could actually end up outside the
  latter. i don't see any of this in our definition *)

  Definition reachable (s: State): Prop :=
    exists i: State, initial i /\ reachable trans i s.

  Definition reachable_alternating (s: State): Prop :=
    exists i: State, initial i /\
      reachable_alternating (fun b => if b then disc_trans else cont_trans) i s.

  Lemma reachable_invariant s: reachable s -> invariant s.
  Proof with auto with real.
    intros.
    destruct H. destruct H.
    induction H0.
      apply invariant_initial...
    destruct H1.
      destruct H1. destruct H2. destruct H3...
    destruct b. destruct c.
    destruct H1. destruct H2. destruct H2.
    simpl in *. subst.
    rewrite curry_inv.
    rewrite <- H3.
    apply H2.
      destruct x...
      simpl.
      apply (CRnonNeg_le_zero x)...
    apply CRle_refl.
  Qed.

  Lemma alternating_reachable s: reachable s -> reachable_alternating s.
  Proof with auto.
    unfold reachable, reachable_alternating.
    intros.
    destruct H. destruct H.
    exists x. split...
    induction H0.
      exists true.
      apply end_with_refl.
    destruct IHreachable...
    destruct H1.
      exists true.
      apply end_with_next with b...
      simpl.
      destruct x...
      apply end_with_next with b...
      apply cont_trans_refl.
      apply reachable_invariant.
      unfold reachable.
      exists a...
    exists false.
    destruct x.
      apply end_with_next with b...
    inversion_clear H2.
      apply end_with_next with b...
      apply end_with_refl.
    simpl in H3.
    apply end_with_next with y...
    apply cont_trans_trans with b...
  Qed.

End transitions_and_reachability.
