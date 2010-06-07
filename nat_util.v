Require Export Arith.
Require Export Peano_dec.
Require Import util.
Require Import EqdepFacts.
Require Import stability.
Require Import tactics.

Set Implicit Arguments.

Local Open Scope nat_scope.

Scheme le_ind_dep := Induction for le Sort Prop.

Lemma le_unique : forall n m (h1 h2 : n <= m), h1 = h2.
Proof.
intro n.
assert (forall m : nat, forall h1 : n <= m, forall p : nat, forall h2 : le n p,
  m=p -> eq_dep nat (le n) m h1 p h2).
 intros m h1; elim h1 using le_ind_dep.
  intros p h2; case h2; intros.
   auto.
   subst n. absurd (S m0 <= m0); auto with arith.
 intros m0 l Hrec p h2. 
  case h2; intros.
   subst n; absurd (S m0 <= m0); auto with arith.
   assert (m0=m1); auto ; subst m0.
   replace l0 with l; auto.
set (w := eq_dep_eq).

   apply (@eq_dep_eq _ eq_nat_dec (le n) m1); auto.
 intros; apply (@eq_dep_eq _ eq_nat_dec (le n) m); auto.
Qed.

Lemma lt_unique : forall n m (h1 h2 : lt n m), h1 = h2.

Proof.
intros n m. unfold lt. intros. apply le_unique.
Qed.

(** Bounded natural numbers *)
(*
Section dom_lt.

  Variable n : nat.

  Local Open Scope nat_scope.

   (* A number smaller than n *)
  Definition dom_lt := { i : nat | i < n }.
  Definition dom_build i (ip : i < n) : dom_lt :=
    @exist _ _ i ip.
  Definition dom_lt_val (ip : dom_lt) : nat := 
    proj1_sig ip.
  Definition dom_lt_proof (ip : dom_lt) : dom_lt_val ip < n := 
    proj2_sig ip.

End dom_lt.
*)

(** Vcheck *)

Section Check_n.

  Variables 
    (n : nat) 
    (P Q : forall i, i < n -> Prop).

  Obligation Tactic := crunch.

  Program Fixpoint check_n_aux (p : nat) (H : p < n) : Prop :=
    let this := @P p H in
    let rest := 
      match p with
      | 0 => True
      | S p' => @check_n_aux p' _
      end
    in
    this /\ rest.

  Program Definition check_n := 
    match n with
    | 0 => True
    | _ => @check_n_aux (pred n) _
    end.

  Variable P_holds : forall i (ip: i < n), P ip.

  Lemma check_n_holds_aux : 
    forall i (ip : i < n), check_n_aux ip.
  Proof.
    induction i; crunch.
  Qed.

  Variable P_stable : forall i (ip: i < n), Stable (P ip).

  Lemma check_n_Stable_aux :
    forall i (ip : i < n), Stable (check_n_aux ip).
  Proof.
    induction i; crunch.
  Qed.

End Check_n.

Lemma check_n_holds n (P : forall i, i < n -> Prop) : 
  (forall i (ip: i < n), P i ip) -> check_n P.
Proof.
  destruct n; crunch.
  apply check_n_holds_aux; crunch.
Qed.

Lemma check_n_Stable n (P : forall i, i < n -> Prop) : 
  (forall i (ip: i < n), Stable (P i ip)) -> Stable (check_n P).
Proof.
  destruct n; crunch.
  apply check_n_Stable_aux; crunch.
Qed.

Section Check_n_equiv.

  Variables 
    (n : nat)
    (P Q : forall i, i < n -> Prop)
    (P_eq_Q : forall i (ip : i < n), P ip <-> Q ip).

  Lemma check_n_equiv_aux : 
    forall i (ip : i < n), 
      check_n_aux P ip <-> check_n_aux Q ip.
  Proof.
     (* FIXME, there must be a better way to state this proof, without 
        those asserts (which essentially break iff into two implications *)
    pose (fun i (ip : i < n) => proj1 (P_eq_Q ip)).
    pose (fun i (ip : i < n) => proj2 (P_eq_Q ip)).
    induction i.
    crunch.
    pose (fun ip : i < n => proj1 (IHi ip)).
    pose (fun ip : i < n => proj2 (IHi ip)).
    crunch.
  Qed.

End Check_n_equiv.

Lemma check_n_equiv n 
  (P Q : forall i, i < n -> Prop)
  (P_eq_Q : forall i (ip : i < n), P i ip <-> Q i ip) :
  check_n P <-> check_n Q.
Proof.
  destruct n; intros.
  crunch.
  unfold check_n.
  match goal with
    | |- check_n_aux _ ?ip <-> check_n_aux _ ?jp =>
      rewrite (lt_unique ip jp)
  end.
  apply check_n_equiv_aux. trivial.
Qed.
