Require Import reachability.
Require Import List.
Set Implicit Arguments.

Section contents.

  Record System: Type :=
    { State: Set
    ; state_eq_dec: forall s s': State, {s=s'}+{s<>s'}
    ; initial: State -> bool
    ; cont_trans: State -> list State
    ; disc_trans: State -> list State
    }.

  Implicit Arguments initial [s].

  Variable system: System.

  Definition reachable (s: State system): Prop :=
    exists i, initial i = true /\
      reachable_alternating i
        (fun a b => List.In b (disc_trans system a))
        (fun a b => List.In b (cont_trans system a)) s.

End contents.
