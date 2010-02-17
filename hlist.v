Require Export Coq.Lists.List.
Require Export Coq.Classes.EquivDec.

Set Implicit Arguments.

(** * Heterogenous lists *)

Section hlists.

  Variable A : Type.
  Variable B : A -> Type.

  Inductive hlist : list A -> Type :=
  | HNil : hlist nil
  | HCons : forall x xs, B x -> hlist xs -> hlist (x::xs)
  .

  Section hlist_get.

    Variable elt : A.

    Inductive member : list A -> Type :=
    | MFirst : forall ls, member (elt :: ls)
    | MNext : forall x ls, member ls -> member (x::ls)
    .
  
    Fixpoint hget lt (l : hlist lt) : member lt -> B elt :=
      match l with
        | HNil => fun p =>
          match p in member lt 
            return 
              match lt with 
              | nil => B elt
              | _ => unit 
              end 
          with
          | MFirst _ => tt
          | MNext _ _ _ => tt
          end
        | HCons _ _ x xs => fun p =>
          match p in member lt
            return 
            match lt with
            | nil => unit
            | x::lt => B x -> (member lt -> B elt) -> B elt
            end
          with
          | MFirst _ => fun x get_xs => x
          | MNext _ _ p' => fun _ get_xs => get_xs p'
          end x (hget xs)
      end.

  End hlist_get.

End hlists.

Implicit Arguments HCons [A B x xs].
