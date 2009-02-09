Require concrete.
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

  Variables (hs: concrete.System) (abs: concrete.State hs -> State system).

  Record Respects: Prop :=
    { RespectsInit: forall s,
        concrete.initial hs s -> initial (abs s) = true
    ; RespectsDisc: forall s1 s2,
       concrete.disc_trans s1 s2 ->
         In (abs s2) (disc_trans system (abs s1))
    ; RespectsCont: forall s1 s2,
       concrete.cont_trans s1 s2 ->
         In (abs s2) (cont_trans system (abs s1))
    }.

  Variable respects: Respects.

  Lemma reachable_alternating_concrete_abstract (s: concrete.State hs):
    concrete.alternating_reachable s -> reachable (abs s).
  Proof with auto.
    unfold concrete.alternating_reachable.
    unfold reachable.
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

  Lemma reachable_concrete_abstract (s: concrete.State hs):
    concrete.reachable s -> reachable (abs s).
  Proof.
    intros. apply reachable_alternating_concrete_abstract.
    apply concrete.reachable_alternating. assumption.
  Qed.

  Theorem safe (s: concrete.State hs):
    ~ reachable (abs s) -> ~ concrete.reachable s.
  Proof.
    intros s H0 H1. apply H0.
    apply reachable_concrete_abstract. assumption.
  Qed.

  Theorem safe' s: ~ reachable s ->
    forall u, abs u = s -> ~ concrete.reachable u.
  Proof. intros. subst. apply safe. assumption. Qed.
    (* hm, these sound good, but can't possible
     be the whole story.. *)

    (* ah, we need something like:
  Theorem safe'' s: ~ abstract.reachable _ s ->
    forall u, u in rsquare(s) -> ~ concrete.reachable u.
     *)

End contents.

(*
Check concrete.invariant.

Require Import Reals.
Open Local Scope R_scope.

Definition Range: Set := prod (option R) (option R).

Definition in_Range (x: R) (r: Range): Prop :=
  match fst r with
  | None => True
  | Some b => b <= x
  end /\
  match snd r with
  | None => True
  | Some b => x <= b
  end.



Definition simple_guard (s: concrete.System) (l: concrete.Location s):
  (exists xr, exists yr, forall p,
    concrete.invariant s (l, p) <-> in_Range (fst p) xr).
*)

