Require Export hybrid.tactics.
Require Export Coq.Lists.List.
Require Export Coq.Program.Program.

Set Implicit Arguments.

Section list_head.

  Variable A : Type.

  Program Definition head (l : list A) : nil <> l -> A :=
    match l as l return l <> [] -> A with
    | [] => fun H => !
    | x::xs => fun _ => x
    end.

End list_head.

Section hlists_def.

  Context `{B : A -> Type}.

  Inductive hlist (l : list A) : Type :=
  | HNil : forall `{l = nil}, hlist l
  | HCons : forall `{H : nil <> l}, B (head H) -> hlist (tail l) -> hlist l.

End hlists_def.

Notation "x ::: xs" := (HCons (H:=@nil_cons _ _ _) x xs) (at level 60).

Section hlists_funs.

  Context `{B : A -> Type, l : list A, a : A}.

  Program Definition hhd (hl : hlist (a::l)) : B a :=
    match hl with
    | HNil _ => !
    | HCons _ x xs => x
    end.

  Program Definition htl (hl : hlist (B:=B) (a::l)) : hlist l :=
    match hl with
    | HNil _ => !
    | HCons _ x xs => xs
    end.

End hlists_funs.
