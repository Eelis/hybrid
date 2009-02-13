Require Import util.
Require Import geometry.
Require Import Fourier.
Require Import reachability.
Set Implicit Arguments.
Open Local Scope R_scope.

Section contents.

  Record flows (X: Set) (f: X -> Time -> X): Prop :=
    { flow_zero: forall x, f x 0 = x
    ; flow_additive: forall x t t', f x (t + t') = f (f x t) t'
    }.
    (* eelis: hm, the one in the paper also takes an input. ours doesn't.
     not needed for thermostat though *)

  Definition product_flow
    (X Y: Set) (fx: X -> Time -> X) (fy: Y -> Time -> Y)
    (xy: prod X Y) (t: Time): prod X Y := (fx (fst xy) t, fy (snd xy) t).

  Lemma product_flows (X Y: Set) (fx: X -> Time -> X) (fy: Y -> Time -> Y):
    flows fx -> flows fy -> flows (product_flow fx fy).
  Proof.
    intros.
    apply Build_flows.
      destruct x. unfold product_flow. simpl.
      rewrite (flow_zero H). rewrite (flow_zero H0). reflexivity.
    intros. destruct x. unfold product_flow. simpl.
    rewrite (flow_additive H). rewrite (flow_additive H0). reflexivity.
  Qed.

  Record System: Type :=
    { Point: Set  (* Continuous States *)
    ; Location: Set (* Locations, the Discrete States *)
     (* This state is finite, but since finiteness is tricky let's wait with a concrete definition *)
      (* eelis: since finiteness of locations seems to be a fundamental property of hybrid systems, it seems to me it really ought to be part of the definition, no? *)

    ; initial: (Location * Point)%type -> Prop

    ; invariant: (Location * Point)%type -> Prop

    ; invariant_initial: forall p, initial p -> invariant p

    ; flow: Location -> Point -> Time -> Point
    ; flow_flows: forall l, flows (flow l)

    ; guard : (Location * Point)%type -> Location -> Prop (* When true discrete step is allowed *)
    ; reset: Location -> Location -> Point -> Point (* reset maps *)
    (* eelis: this separation of guard and reset seems to cause a problem:
    the paper allows having different transitions from a given (l, x) to
    some (l', x'), because you can have different transitions. we only allow one! *)
    }.

  Implicit Arguments initial [s].
  Implicit Arguments invariant [s].

  Variable system: System.

  Definition State: Set := (Location system * Point system)%type.

  Definition cont_trans (s s': State) : Prop :=
    fst s = fst s' /\ exists d:Duration,
      (forall t, 0 <= t <= proj1_sig d ->
        invariant (fst s, flow system (fst s) (snd s) t))
      /\ flow system (fst s') (snd s) (proj1_sig d) = (snd s').

  Definition disc_trans (s s': State) : Prop :=
    guard system s (fst s') /\
     reset system (fst s) (fst s') (snd s) = (snd s') /\
      invariant s /\ invariant s'.

  Definition trans (s s': State): Prop := disc_trans s s' \/ cont_trans s s'.

  Notation "s ->_C s'" := (cont_trans s s') (at level 70).
  Notation "s ->_D s'" := (disc_trans s s') (at level 70).
  Notation "s --> s'" := (trans s s') (at level 90).

  Lemma cont_trans_refl s: invariant s -> s ->_C s.
  Proof with auto.
    intros. unfold cont_trans. destruct s.
    split...
    exists immediately.
    unfold immediately. simpl.
    split.
      intros.
      replace t with 0.
        rewrite (flow_zero (flow_flows system l))...
      destruct H0.
      apply Rle_antisym...
    apply (flow_zero (flow_flows system l)).
  Qed.

  Lemma cont_trans_trans s s' s'':
    (s ->_C s') -> (s' ->_C s'') -> (s ->_C s'').
  Proof with auto.
    unfold cont_trans.
    intros. destruct s. destruct s'. destruct s''.
    simpl in *.
    destruct H. destruct H1. destruct H1. subst.
    destruct H0. destruct H0. destruct H0. subst.
    split...
    exists (duration_plus x x0).
    split.
      simpl.
      intros.
      destruct x. destruct x0.
      simpl in *.
      assert (forall t, 0 <= t <= x0 -> invariant (l1, flow system l1 p (x + t))).
        intros.
        rewrite (flow_additive (flow_flows system l1))...
      clear H0.
      set (Rge_le _ _ r).
      set (Rge_le _ _ r0).
      destruct H.
      destruct (Rle_lt_dec t x)...
      set (H2 (t - x)).
      rewrite Rplus_minus in i.
      apply i.
      split; fourier.
    rewrite <- (flow_additive (flow_flows system l1))...
  Qed.

  Lemma cont_trans_preserves_location s s':
    s ->_C s' -> fst s = fst s'.
  Proof. firstorder. Qed.

  (* eelis: hm, the paper distinguishes between R^n and the
  subset that is the continuous state space for the HS, and i
  seem to recall that flowing could actually end up outside the
  latter. i don't see any of this in our definition *)

  Definition reachable (s: State): Prop :=
    exists i: State, initial i /\ reachable_from i trans s.

  Definition alternating_reachable (s: State): Prop :=
    exists i: State, initial i /\
      reachable_alternating i disc_trans cont_trans s.

  Lemma reachable_invariant s: reachable s -> invariant s.
  Proof with auto with real.
    intros.
    unfold reachable in H.
    destruct H.
    destruct H.
    induction H0.
      apply invariant_initial...
    destruct H1.
      firstorder.
    destruct s. destruct s'.
    destruct H1. destruct H2. destruct H2.
    simpl in *. subst.
    apply H2.
    destruct x0...
  Qed.

  Lemma reachable_alternating s: reachable s -> alternating_reachable s.
  Proof with auto.
    unfold reachable, alternating_reachable.
    intros.
    destruct H.
    exists x.
    firstorder.
    induction H0.
      apply reachable_alternating_A.
      apply reachable_alternating_a_init.
    destruct IHreachable_from.
      destruct H1.
        apply reachable_alternating_A.
        apply reachable_alternating_a_next with s s...
        apply cont_trans_refl.
        apply reachable_invariant.
        exists x...
      apply reachable_alternating_B with s...
    destruct H1.
      apply reachable_alternating_A.
      rename x into init.
      apply reachable_alternating_a_next with s s'0...
    apply reachable_alternating_B with s...
    apply cont_trans_trans with s'0...
  Qed.

  Definition Trace := nat -> State.
    (* eelis: hm, this doesn't say what transitions were used. since
    a HS can contain duplicate transitions (at least in the paper),
    this means we cannot distinguish between traces those *)
    (* eelis: hm, with this, you'd encode finite traces with a repeating
    last trace? but that's indistinguishable from an infinite trace which
    just happens to do lots of continuous transitions of duration 0 !
    perhaps a coinductive type of _potentially_ infinite lists would
    be better suited. or is the idea that there's no such thing as a
    finite trace? *)

  Definition Trans_prop (t:Trace): Prop :=
    forall n:nat, t n --> t (S n).

  CoInductive EelisTrace (start: State): Set :=
    | empty_trace
    | trace_trans next: (start --> next) -> EelisTrace next -> EelisTrace start.
    (* just a thought.. *)

End contents.
