Require Export hybrid.tactics.
Require Export Coq.Lists.List.
Require Export Coq.Classes.EquivDec.
Require Import Coq.Logic.Eqdep_dec.

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

  Section hlist_eqdec.

    Variable l : list A.
    Variable EltsEqDec : forall x, In x l -> EqDec (B x) eq.

    Lemma hlist_eq_fst_eq a l (x y : B a) (xs ys : hlist l) :
       HCons x xs === HCons y ys ->
       x === y.
    Proof.
      intros.
    Admitted.

    Lemma hlist_eq_snd_eq a l (x y : B a) (xs ys : hlist l) :
       HCons x xs === HCons y ys ->
       xs === ys.
    Proof.
    Admitted.

    Hint Resolve hlist_eq_fst_eq hlist_eq_snd_eq : hlists.

    Global Program Instance hlist_EqDec : EqDec (hlist l) eq.
    Next Obligation.
      revert x y; induction l; intros; 
        dep_destruct x; dep_destruct y.
      intuition.
      assert (a_al0 : In a (a :: l0)) by intuition.
      destruct (EltsEqDec a_al0 b b0).
      assert (IHpre : forall x, In x l0 -> EqDec (B x) eq) by intuition.
      destruct (IHl0 IHpre x1 x0).
       (* FIXME, why subst* does not work here? *)
      rewrite e. rewrite e0. intuition.
      compute. intuition eauto with hlists.
      compute. intuition eauto with hlists.
    Qed.

  End hlist_eqdec.

End hlists.

Implicit Arguments HCons [A B x xs].
