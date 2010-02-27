Require Export hybrid.tactics.
Require Export Coq.Lists.List.
Require Export Coq.Program.Program.

Set Implicit Arguments.

Section list_head.

  Variable A : Type.

  Program Definition head (l : list A) : l <> nil -> A :=
    match l as l return l <> [] -> A with
    | [] => fun H => !
    | x::xs => fun _ => x
    end.

End list_head.

Section hlists_def.

  Context `{B : A -> Type}.

  Inductive hlist (l : list A) : Type :=
  | HNil : forall `{l = nil}, hlist l
  | HCons : forall `{H : l <> nil}, B (head H) -> hlist (tail l) -> hlist l.

End hlists_def.
