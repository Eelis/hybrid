Require geometry.
Require Import bnat.
Require Import util c_util.
Require abstract abstraction.

Set Implicit Arguments.

Open Scope CR_scope.

Section contents.

  Variables
    (chs: concrete.System)
    (component: unary_setoid_morphism (concrete.Point chs) CRasCSetoid).

  Add Morphism component with signature (@cs_eq _) ==> (@cs_eq _) as component_mor.
  Proof. intros. apply usm_wd; auto. Qed.

  Inductive IntervalSpec: Q -> nat -> Type :=
    | highest b: IntervalSpec b 0
    | bound: forall (nb ob: Q) (p: (nb <= ob)%Q) (l: nat),
        IntervalSpec ob l -> IntervalSpec nb (S l).

  Definition spec_bounds b n: IntervalSpec b n -> bnat (S n) -> geometry.OpenQRange.
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

  Definition bounds b n: IntervalSpec b n -> bnat (S (S n)) -> geometry.OpenQRange.
    intros b n s i.
    destruct (bnat_cases i) as [[p A] | B].
      exact (spec_bounds s p).
    exact (geometry.qbelow b).
  Defined.

  Definition spec_interval b n (s: IntervalSpec b n) (p: concrete.Point chs):
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

  Definition select_interval b n (s: IntervalSpec b n) l p: concrete.invariant (l, p) ->
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
    (inv_lower: forall l p, concrete.invariant (l, p) -> 'b <= component p)
    l p: concrete.invariant (l, p) ->
    sig (fun i => geometry.in_orange (spec_bounds s i) (component p)).
  Proof with auto.
    intros.
    destruct (spec_interval s p).
      destruct s0.
      exists x...
    elimtype False.
    apply CRlt_le_asym with (component p) ('b); eauto.
  Qed.

  Variables (b: Q) (n: nat) (s: IntervalSpec b n).

  Definition Region := bnat (S (S n)).

  Require interval_abstraction.

  Definition ap: abstract.Parameters chs :=
    interval_abstraction.parameters chs component (NoDup_bnats _) (bounds s) (select_interval s).

  Definition ap' (UH: forall l p, concrete.invariant (l, p) -> ' b <= component p):
    abstract.Parameters chs :=
      interval_abstraction.parameters chs component (NoDup_bnats _) (spec_bounds s) (select_interval' s UH).

End contents.

Implicit Arguments bound [ob l].
