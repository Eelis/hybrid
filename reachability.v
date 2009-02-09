Set Implicit Arguments.

Section contents.

  Variables
    (State: Set) (init: State)
    (trans: State -> State -> Prop).

  Inductive reachable_from: State -> Prop :=
    | reachable_from_init: reachable_from init
    | reachable_from_next s s': reachable_from s ->
        trans s s' -> reachable_from s'.

  Variables  (atrans btrans: State -> State -> Prop).

  Inductive reachable_alternating_a: State -> Prop :=
    | reachable_alternating_a_init:
        reachable_alternating_a init
    | reachable_alternating_a_next s s' s'':
        reachable_alternating_a s ->
        btrans s s' -> atrans s' s'' ->
        reachable_alternating_a s''.

  Inductive reachable_alternating: State -> Prop :=
    | reachable_alternating_A s:
        reachable_alternating_a s -> reachable_alternating s
    | reachable_alternating_B s s':
        reachable_alternating_a s ->
        btrans s s' -> reachable_alternating s'.

End contents.
