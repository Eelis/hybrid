Require Export Bool.
Require Setoid.

Set Implicit Arguments.

Section beq.

  Variable A : Type.
  Variable beq : A -> A -> bool.
  Variable beq_ok : forall x y, beq x y = true <-> x = y.

  Lemma beq_refl : forall x, beq x x = true.
  Proof.
    intros. rewrite (beq_ok x x). reflexivity.
  Qed.

End beq.

Lemma andb_intro : forall a b, a = true -> b = true -> a && b = true.
Proof.
  intros. subst. reflexivity.
Qed.

Lemma andb_elim : forall a b, a && b = true -> a = true /\ b = true.
Proof.
  destruct a; destruct b; intuition.
Qed.

Lemma band_discr : forall b1 b2,
  b1 = true ->
  b2 = true ->
  ~(b1 && b2 = false).
Proof.
  intros. subst. discriminate.
Qed.

Lemma bool_case : forall b, {b = true} + {b = false}.
Proof.
  destruct b; auto.
Qed.

Lemma not_false_true b : b = true -> b <> false.
Proof.
  intros. destruct b; discriminate. 
Qed.

Ltac band_discr :=
  match goal with
  | _: ?X && ?Y = false |- _ => apply (@band_discr X Y); trivial
  end.

Ltac bool_solver :=
  match goal with
  | |- ?X && ?Y = true =>
      eapply (proj2 (andb_true_iff _ _)); split; bool_solver
  | _ => idtac
  end.
