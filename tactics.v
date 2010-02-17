Require Export Coq.Program.Program.

Ltac dep_destruct E :=
  let x := fresh "x" in
    remember E as x; simpl in x; dependent destruction x;
      try match goal with
            | [ H : _ = E |- _ ] => rewrite <- H in *; clear H
          end.
