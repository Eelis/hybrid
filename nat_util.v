Require Export Arith.
Require Export Peano_dec.
Require Import util.
Require Import EqdepFacts.

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
    (P : forall i, i < n -> Prop).

  Program Fixpoint check_n_aux (p : nat | p <= n) 
    {measure (fun p => n - p) p} : Prop :=

    match le_lt_dec n p with
    | left _ => True
    | right cmp =>
        @P p cmp /\ @check_n_aux (S p)
    end.

  Next Obligation.
  Proof.
    omega.
  Qed.

  Program Definition check_n := @check_n_aux 0.

  Next Obligation.
  Proof.
    omega.
  Qed.

  Lemma check_n_holds : 
    (forall i (ip: i < n), P ip) -> check_n.
  Proof.
  Admitted.

End Check_n.

Section Check_n_equiv.

  Variables 
    (n : nat)
    (P Q : forall i, i < n -> Prop).

  Lemma check_n_equiv : 
    (forall i (ip : i < n), P ip <-> Q ip) ->
    (check_n P <-> check_n Q).
  Proof.
  Admitted.

End Check_n_equiv.