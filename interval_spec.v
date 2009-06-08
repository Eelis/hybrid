Require geometry.
Require Import bnat.
Require Import c_util.

Set Implicit Arguments.

Section contents.

  Inductive IntervalSpec: Q -> nat -> Type :=
    | highest b: IntervalSpec b 0
    | bound: forall (nb ob: Q) (p: (nb <= ob)%Q) (l: nat),
        IntervalSpec ob l -> IntervalSpec nb (S l).

  Definition spec_bounds r n: IntervalSpec r n -> bnat (S n) -> geometry.OpenQRange.
    apply (IntervalSpec_rect
      (fun cr n _ => bnat (S n) -> geometry.OpenQRange) (fun q _ => geometry.qabove q)).
    intros nb ob.
    intros.
    destruct (bnat_cases H0).
      destruct s.
      subst.
      apply (H x).
    subst.
    exists (Some nb, Some ob).
    assumption.
  Defined.

  Definition bounds r n: IntervalSpec r n -> bnat (S (S n)) -> geometry.OpenQRange.
    intros.
    destruct (bnat_cases H0) as [[p A] | B].
      exact (spec_bounds H p).
    exact (geometry.qbelow r).
  Defined.

  Variables (Location Point: Type)
    (component: Point -> CR)
    (invariant: Location * Point -> Prop).

  Open Scope CR_scope.

  Definition spec_interval b n (s: IntervalSpec b n) (p: Point):
   sig (fun i => geometry.in_orange (spec_bounds s i) (component p)) + (component p < 'b).
  Proof with simpl; auto.
    induction s; intro p'.
      simpl spec_bounds.
      destruct (CR_le_lt_dec ('b) (component p'))...
      left. exists (bO 0). unfold geometry.in_orange...
    destruct (CR_le_lt_dec ('nb) (component p')); [left | right]...
    destruct (IHs p').
      destruct s0.
      exists (bS x)...
    exists (bO (S l)).
    unfold geometry.in_orange...
  Qed.

  Definition select_interval b n (s: IntervalSpec b n) l (p: Point): invariant (l, p) ->
    sig (fun i => geometry.in_orange (bounds s i) (component p)).
  Proof with simpl; auto.
    intros.
    destruct (spec_interval s p).
      destruct s0.
      exists (bS x)...
    exists (bO (S n)).
    split...
  Qed.

  Definition select_interval' b n (s: IntervalSpec b n)
    (inv_lower: forall l p, invariant (l, p) -> 'b <= component p) l (p: Point): invariant (l, p) ->
    sig (fun i => geometry.in_orange (spec_bounds s i) (component p)).
  Proof with auto.
    intros.
    destruct (spec_interval s p).
      destruct s0.
      exists x...
    elimtype False.
    apply CRlt_le_asym with (component p) ('b); eauto.
  Qed.

End contents.

Implicit Arguments bound [ob l].
