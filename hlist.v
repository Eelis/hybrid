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

    Hint Resolve hlist_eq_fst_eq hlist_eq_snd_eq.

    Global Program Instance hlist_EqDec : EqDec (hlist l) eq.
    Next Obligation.
      revert x y; induction l; intros;
        repeat 
          match goal with
          | hl : hlist [] |- _ => dep_destruct hl
          | hl : hlist (_::_) |- _ => dep_destruct hl
          end;
        crunch;
        match goal with
        | EQ : forall x, ?a = x \/ In x ?l -> _, x : B ?a, y : B ?a 
            |- context [HCons ?x _ === HCons ?y _] =>
            let a_al0 := fresh "a_al0" in
            assert (a_al0 : In a (a :: l0)) by intuition;
            destruct (EQ a a_al0 x y)
        end;
        match goal with
        | IH : (forall x, In x ?l -> EqDec (?B x) eq) -> forall x y, {x === y} + {x =/= y} 
            |- context [HCons _ ?xs === HCons _ ?ys] =>
            let IHpre := fresh "IHpre" in
            assert (IHpre : forall x, In x l -> EqDec (B x) eq) by intuition;
            destruct (IH IHpre xs ys)
        end;
        simpl_eqs; crunch; compute; crunch.
    Qed.

  End hlist_eqdec.

End hlists.

Implicit Arguments HCons [A B x xs].
