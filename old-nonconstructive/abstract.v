Require Import reachability.
Require Import List.
Require Import util.
Set Implicit Arguments.

Record System: Type :=
  { State: Set
  ; state_eq_dec: forall s s': State, decision (s=s')
  ; states: list State
  ; states_exhaustive: forall s, In s states
  ; initial: State -> bool
  ; cont_trans: State -> list State
  ; disc_trans: State -> list State
      (* hm, why do we need to distinguish between these? *)
  }.

Implicit Arguments initial [s].
Implicit Arguments cont_trans [s].
Implicit Arguments disc_trans [s].

Definition reachable {system: System} (s: State system): Prop :=
  exists i, initial i = true /\
    reachable_alternating i
      (fun a b => In b (disc_trans a))
      (fun a b => In b (cont_trans a)) s.
