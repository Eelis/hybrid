Require concrete.
Require abstract.
Require Import reachability.
Require Import List.
Set Implicit Arguments.

Section contents.

  Variables (chs: concrete.System) (ahs: abstract.System)
    (abs: concrete.State chs -> abstract.State ahs).

  Record Respects: Prop :=
    { RespectsInit: forall s,
        concrete.initial chs s -> abstract.initial ahs (abs s) = true
    ; RespectsDisc: forall s1 s2,
       concrete.disc_trans s1 s2 ->
         In (abs s2) (abstract.disc_trans ahs (abs s1))
    ; RespectsCont: forall s1 s2,
       concrete.cont_trans s1 s2 ->
         In (abs s2) (abstract.cont_trans ahs (abs s1))
    }.

  Variable respects: Respects.

  Lemma reachable_alternating_concrete_abstract (s: concrete.State chs):
    concrete.alternating_reachable s -> abstract.reachable ahs (abs s).
  Proof with auto.
    unfold concrete.alternating_reachable.
    unfold abstract.reachable.
    intros.
    destruct H.
    destruct H.
    exists (abs x).
    split. firstorder.
    destruct H0.
      apply reachable_alternating_A.
      induction H0.
        apply reachable_alternating_a_init.
      destruct respects.
      apply reachable_alternating_a_next with (abs s) (abs s')...
    apply reachable_alternating_B with (abs s).
      clear H1.
      induction H0.
        apply reachable_alternating_a_init.
      destruct respects.
      apply reachable_alternating_a_next with (abs s) (abs s'0)...
    destruct respects...
  Qed.

  Lemma reachable_concrete_abstract (s: concrete.State chs):
    concrete.reachable s -> abstract.reachable ahs (abs s).
  Proof.
    intros. apply reachable_alternating_concrete_abstract.
    apply concrete.reachable_alternating. assumption.
  Qed.

  Theorem safe (s: concrete.State chs):
    ~ abstract.reachable ahs (abs s) -> ~ concrete.reachable s.
  Proof.
    intros s H0 H1. apply H0.
    apply reachable_concrete_abstract. assumption.
  Qed.

  Theorem safe' s: ~ abstract.reachable ahs s ->
    forall u, abs u = s -> ~ concrete.reachable u.
  Proof. intros. subst. apply safe. assumption. Qed.
    (* hm, these sound good, but can't possible
     be the whole story.. *)

    (* ah, we need something like:
  Theorem safe'' s: ~ abstract.reachable _ s ->
    forall u, u in rsquare(s) -> ~ concrete.reachable u.
     *)

End contents.
