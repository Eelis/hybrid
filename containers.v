Require Import util list_util.
Require List.

Set Implicit Arguments.

Class Container (Elem C: Type) := In: Elem -> C -> Prop.
Hint Unfold In.

Notation "x ∈ y" := (In x y) (at level 40).
Notation "x ∉ y" := (In x y -> False) (at level 40).

Instance predicate_container {X}: Container X (X -> Prop) := fun x p => p x.
Hint Unfold predicate_container.

Instance list_container X: Container X (List.list X) := @List.In X.
Implicit Arguments list_container [].

Instance bool_pred_container X: Container X (X -> bool) := fun x p => p x = true.
Implicit Arguments bool_pred_container [].

Section ops_and_props.

  Context `{Container A X}.

  Definition is_empty (x: X): Prop := forall a, a ∉ x.
  Definition nonempty (x: X): Prop := exists a, a ∈ x.

  Context `{Container A Y}.

  Definition intersection (c: X) (d: Y) (x: A): Prop := x ∈ c /\ x ∈ d.
  Definition incl (x: X) (y: Y) := forall a, a ∈ x -> a ∈ y.

End ops_and_props.

Notation "x ∩ y" := (intersection x y) (at level 30).
Notation "x ⊆ y" := (incl x y) (at level 40).

Definition overlap `{Container A X} `{Container A Y} (c: X) (d: Y): Prop := nonempty (c ∩ d).

Hint Unfold intersection incl.
