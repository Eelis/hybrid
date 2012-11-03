Set Automatic Coercions Import.

Require Import util c_util flow stability containers Morphisms.
Require EquivDec.
Set Implicit Arguments.

Open Local Scope CR_scope.

Record System: Type :=
  { Point: CSetoid

  ; Location: Set
  ; Location_eq_dec: EquivDec.EqDec Location eq

  ; State := Location * Point

  ; locations: ExhaustiveList Location
  ; NoDup_locations: NoDup locations

  ; initial: Location * Point -> Prop

(*
  ; invariant': morpher (@eq Location ==> @cs_eq Point ==> iff)%signature
*)

  ; invariant: Location * Point -> Prop
  ; invariant_initial: initial ⊆ invariant
  ; invariant_mor: Proper ((@eq _) ==> (@cs_eq _) ==> iff) (curry invariant)
    (* hm, can't we just use a unary morphism with product setoid equality on State? *)
  ; invariant_stable: forall s, Stable (invariant s)

  ; flow: Location -> Flow Point

  ; guard: Location * Point -> Location -> Prop
  ; reset: Location -> Location -> Point -> Point
    (* this separation of guard and reset seems to cause a problem:
    the paper allows having different transitions from a given (l, x) to
    some (l', x'), because you can have different transitions. we only allow one! *)
  }.

Existing Instance invariant_mor.

Hint Resolve Location_eq_dec locations: typeclass_instances.

Implicit Arguments Build_System [Point Location invariant initial].
Implicit Arguments initial [s].
Implicit Arguments invariant [[s]].

Section transitions_and_reachability.

  Variable system: System.

  Let State: Type := State system.
  Definition location: State -> Location system := fst.
  Definition point: State -> Point system := snd.

  Definition can_flow l: relation (Point system) := fun p p' =>
    exists d: Duration,
      (forall t, 0 <= t -> t <= `d -> invariant (l, flow system l p t))%CR
      /\ flow system l p (`d) [=] p'.

  Definition cont_trans: relation State := fun s s' =>
    location s = location s' /\
    can_flow (location s) (point s) (point s').

  Definition disc_trans: relation State := fun s s' =>
    guard system s (location s') /\
     reset system (location s) (location s') (point s) = point s' /\
      invariant s /\ invariant s'.

  Definition trans: relation State
    := fun s s' => disc_trans s s' \/ cont_trans s s'.

  Notation "s ->_C s'" := (cont_trans s s') (at level 70).
  Notation "s ->_D s'" := (disc_trans s s') (at level 70).
  Notation "s ->_T s'" := (trans s s') (at level 90).

  Lemma cont_trans_refl s: invariant s -> s ->_C s.
  Proof with auto.
    revert s.
    intros [l p] H.
    split...
    exists NonNegCR_zero.
    split. intros.
      rewrite (curry_eq (@invariant system)),
        (snd (CRle_def t 0)), flow_zero...
    apply flow_zero.
  Qed.

  Hint Resolve cont_trans_refl.
  Hint Resolve invariant_stable.

  Lemma cont_trans_trans: Transitive cont_trans.
  Proof with auto.
    intros [l p] [l' p'] [l'' p''] [ll' [t [i f]]] [l'l'' [t' [i' f']]].
    simpl location in *. simpl point in *. subst.
    split...
    exists (NonNegCR_plus t t').
    destruct t as [t nt]. destruct t' as [t' nt'].
    split.
      simpl proj1_sig in *.
      intros. simpl.
      apply (DN_apply (CRle_dec t t0))...
      intros [A | B]...
      rename t0 into x.
      rewrite
        (curry_eq (@invariant system)),
        (t11 t x),
        (flow_additive (flow system l'') p t (x - t)),
        f.
      apply i'.
        rewrite <- (Ropp_def CR_ring_theory t).
        apply t2...
      rewrite (t11 t t').
      rewrite (Radd_assoc CR_ring_theory).
      apply t2...
    simpl. rewrite flow_additive, f...
  Qed.

  Hint Resolve cont_trans_trans.

  Lemma cont_trans_preserves_location s s': s ->_C s' -> fst s = fst s'.
  Proof. intros. destruct H; auto... Qed.

  (* hm, the paper distinguishes between R^n and the
  subset that is the continuous state space for the HS, and i
  seem to recall that flowing could actually end up outside the
  latter. i don't see any of this in our definition *)

  Definition reachable (s: State): Prop :=
    exists i: State, initial i /\ trans_refl_closure.R trans i s.

  Definition unreachable (s: State): Prop := ~ reachable s.

  Hint Unfold reachable.

  Definition trans_kind (b: bool) := if b then disc_trans else cont_trans.

  Hint Unfold trans_kind.

  Definition reachable_alternating (s: State): Prop :=
    exists i: State, initial i /\ alternate trans_kind i s.

  Lemma reachable_invariant: reachable ⊆ invariant.
  Proof with auto with real.
    intros dst [src [src_init src_reach_dst]].
    induction src_reach_dst as [ | s [l' p'] [l'' p''] R IH T].
      apply invariant_initial...
    destruct T as [[_ [_ [_ H]]] | [A [B [C D]]]]...
    simpl in A. subst.
    unfold In, predicate_container.
    rewrite (curry_eq invariant).
    rewrite <- D.
    apply C...
    apply (CRnonNeg_le_zero (`B))...
  Qed.

  Lemma alternating_reachable: forall s, reachable_alternating s <-> reachable s.
  Proof with eauto.
    split.
      intros [s' [i [b t]]].
      exists s'.
      split... clear i.
      induction t...
      apply trans_refl_closure.step with y...
      destruct b; [left | right]...
    intros [x [H H0]].
    exists x. split...
    induction H0. exists true...
    destruct IHR...
    destruct H1; [exists true | exists false]; destruct x...
      apply end_with_next with b...
      apply end_with_next with b...
      apply cont_trans_refl.
      apply reachable_invariant.
      eauto 20.
    inversion_clear H2...
  Qed.

End transitions_and_reachability.

Implicit Arguments reachable [[system]].
Implicit Arguments unreachable [[system]].
Hint Unfold cont_trans.
Hint Unfold can_flow.
