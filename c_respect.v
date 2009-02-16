Require c_concrete.
Require abstract.
Require Import reachability.
Require Import List.
Set Implicit Arguments.

Section contents.

  Variables (chs: c_concrete.System) (ahs: abstract.System)
    (abs: c_concrete.State chs -> abstract.State ahs).

  Record Respects: Prop :=
    { RespectsInit: forall s,
        c_concrete.initial s -> abstract.initial (abs s) = true
    ; RespectsDisc: forall s1 s2,
       c_concrete.disc_trans s1 s2 ->
         In (abs s2) (abstract.disc_trans (abs s1))
    ; RespectsCont: forall s1 s2,
       c_concrete.cont_trans s1 s2 ->
         In (abs s2) (abstract.cont_trans (abs s1))
    }.

  Variable respects: Respects.

  Lemma reachable_alternating_concrete_abstract (s: c_concrete.State chs):
    c_concrete.alternating_reachable s -> abstract.reachable (abs s).
  Proof with auto.
    unfold c_concrete.alternating_reachable.
    unfold abstract.reachable.
    intros.
    destruct H.
    destruct H.
    exists (abs x).
    destruct respects...
    split...
    destruct H0.
      apply reachable_alternating_A.
      induction H0.
        apply reachable_alternating_a_init.
      apply reachable_alternating_a_next with (abs s) (abs s')...
    apply reachable_alternating_B with (abs s)...
    clear H1.
    induction H0.
      apply reachable_alternating_a_init.
    apply reachable_alternating_a_next with (abs s) (abs s'0)...
  Qed.

  Lemma reachable_concrete_abstract (s: c_concrete.State chs):
    c_concrete.reachable s -> abstract.reachable (abs s).
  Proof.
    intros. apply reachable_alternating_concrete_abstract.
    apply c_concrete.reachable_alternating. assumption.
  Qed.

  Theorem safe (s: c_concrete.State chs):
    ~ abstract.reachable (abs s) -> ~ c_concrete.reachable s.
  Proof.
    intros s H0 H1. apply H0.
    apply reachable_concrete_abstract. assumption.
  Qed.

  Theorem safe' s: ~ abstract.reachable s ->
    forall u, abs u = s -> ~ c_concrete.reachable u.
  Proof. intros. subst. apply safe. assumption. Qed.
    (* hm, these sound good, but can't possible
     be the whole story.. *)

    (* ah, we need something like:
  Theorem safe'' s: ~ abstract.reachable _ s ->
    forall u, u in rsquare(s) -> ~ concrete.reachable u.
     *)

End contents.
