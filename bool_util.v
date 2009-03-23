Require Export Bool.

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
