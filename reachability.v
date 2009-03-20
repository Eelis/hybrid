Require Import util.
Set Implicit Arguments.

Section definitions.

  Variables (State: Type) (trans: State -> State -> Prop).

  Inductive reachable: State -> State -> Prop :=
    | reachable_refl s: reachable s s
    | reachable_next a b c: reachable a b ->
        trans b c -> reachable a c.

  Inductive path: State -> State -> Type :=
    | path_refl s: path s s
    | path_next a b c: path a b -> trans b c -> path a c.

  Lemma reachable_trans a b: reachable a b -> forall c, reachable b c ->
    reachable a c.
  Proof with auto.
    intros.
    induction H0...
    apply reachable_next with b...
  Qed.

  Inductive reachable_irrefl: State -> State -> Prop :=
    | reachable_one s s': trans s s' -> reachable_irrefl s s'
    | reachable_more a b c: reachable_irrefl a b ->
        trans b c -> reachable_irrefl a c.

  Lemma reachable_flip (P: State -> Prop) (Pdec: forall s, decision (P s))
   (a b: State): reachable a b -> P a -> ~ P b ->
    exists c, exists d, P c /\ ~ P d /\ trans c d.
  Proof with auto.
    intros P Pdec a b r. induction r.
      intros. elimtype False...
    intros.
    destruct (Pdec b)...
    exists b. exists c...
  Qed.

  Lemma reachable_flip_inv (P: State -> Prop) (Pdec: forall s, decision (P s))
   (a b: State): reachable a b -> ~ P a -> P b ->
    exists c, exists d, ~ P c /\ P d /\ trans c d.
  Proof with auto.
    intros P Pdec a b r. induction r.
      intros. elimtype False...
    intros.
    destruct (Pdec b)...
    exists b. exists c...
  Qed.

  Variable t: bool -> State -> State -> Prop.

  Inductive end_with: bool -> State -> State -> Prop :=
    | end_with_refl b s: end_with b s s
    | end_with_next b x y:
        end_with (negb b) x y -> forall z, t b y z -> end_with b x z.

  Definition reachable_alternating (s s': State): Prop :=
    exists b, end_with b s s'.

End definitions.
