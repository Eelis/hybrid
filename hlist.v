Require Export hybrid.tactics.
Require Export hybrid.util.
Require Export Coq.Lists.List.
Require Export Coq.Classes.EquivDec.
Require Import Coq.Logic.Eqdep_dec.

Set Implicit Arguments.

(** * Heterogenous lists *)

Section hlists.

  Variable A : Type.
  Variable B : A -> Type.

  (* heterogenous list parametrized by 'list signature' *)
  Inductive hlist : list A -> Type :=
  | HNil : hlist nil
  | HCons : forall x xs, B x -> hlist xs -> hlist (x::xs)
  .

  (* [hget] on [HList]s is similar to [Vnth] on [vector]s *)
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

  (* decidability of Leibniz equality on [HList]s (given 
     decidable equality on all types of its elements). *)
  Section hlist_eqdec.

    Variable lt : list A.
    Variable EltsEqDec : forall x, In x lt -> EqDec (B x) eq.

    Lemma hlist_eq_fst_eq a lt (x y : B a) (xs ys : hlist lt) :
       HCons x xs === HCons y ys ->
       x === y.
    Proof.
      inversion 1; dep_subst; intuition.
    Qed.

    Lemma hlist_eq_snd_eq a lt (x y : B a) (xs ys : hlist lt) :
       HCons x xs === HCons y ys ->
       xs === ys.
    Proof.
      inversion 1; dep_subst; intuition.
    Qed.

    Hint Resolve hlist_eq_fst_eq hlist_eq_snd_eq.

    Global Program Instance hlist_EqDec : EqDec (hlist lt) eq.
    Next Obligation.
      revert x y; induction lt; intros;
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
            assert (a_al0 : In a (a :: l)) by intuition;
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

  (* [hsingleton x] is a [HList] with only one element [x] *)
  Definition hsingleton (t : A) (x : B t) : hlist [t] := HCons x HNil.

  (* [hhd] of [x::xs] is [x] *)
  Definition hhd lt (l : hlist lt) :=
    match l in hlist lt
      return match lt with
             | nil => unit
             | x::_ => B x
             end
    with
    | HNil => tt
    | HCons _ _ x _ => x
    end.

  (* [htl] of [x::xs] is [xs] *)
  Definition htl lt (l : hlist lt) :=
    match l in hlist lt
      return match lt with
             | nil => unit
             | _ :: lt' => hlist lt'
             end 
    with
    | HNil => tt
    | HCons _ _ _ tl => tl
    end.

  (* [happ [x_1; ... x_n] [y_1; ... y_n] = [x_1; ... x_n; y_1; ... y_n]] *)
  Fixpoint happ (lt1 : list A) (l1 : hlist lt1) : 
    forall lt2, hlist lt2 -> hlist (lt1 ++ lt2) :=
    match l1 in hlist lt1 
      return forall lt2, hlist lt2 -> hlist (lt1 ++ lt2) 
    with
    | HNil => fun _ l2 => l2
    | HCons _ _ x l1' => fun _ l2 => HCons x (happ l1' l2)
    end.

  Variable f : forall x, B x.

  (* [hbuild [t_1; ... t_n] = [f t_1; ... f t_n]] *)
  Fixpoint hbuild (lt : list A) : hlist lt :=
    match lt with
    | nil => HNil
    | x::lt' => HCons (f x) (hbuild lt')
    end.

End hlists.

Implicit Arguments HNil [A B].
Implicit Arguments HCons [A B x xs].

Infix ":::" := HCons (right associativity, at level 60).
Infix "+++" := happ (right associativity, at level 60).

Section HList_prods.

  Variable A : Type.
  Variable B : A -> Type.

  (* [hlist_combine [x_1; ... x_n] [y_1; ... y_n] = 
     [x_1::y_1; ... x_n::y_n; x_2::y_1 ... x_n::y_n]] *)
  Fixpoint hlist_combine t (l : list t)
    : forall ts, list (hlist id ts) -> list (hlist id (t::ts)) :=
    match l return 
      forall ts, list (hlist id ts) -> list (hlist id (t::ts)) 
    with
    | [] => fun _ _ => []
    | x::xs => fun _ l' => 
        map (fun y_i => (x : id t):::y_i) l' ++ hlist_combine xs l'
    end.

  Fixpoint hlist_prod_tuple (l : list Type) (hl : hlist (fun T => list T) l) 
    : list (hlist id l) :=
    match hl in hlist _ l return list (hlist id l) with
    | HNil => [HNil]
    | HCons _ _ x l' => hlist_combine x (hlist_prod_tuple l')
    end.

End HList_prods.

(*
Eval vm_compute in hlist_prod_tuple ([1; 2]:::[false;true]:::HNil).
*)

Section ExhaustiveHList.

  Variable A : Type.
  Variable B : A -> Type.
  Variable l : list A.

  Context `{EL : forall x, In x l -> ExhaustiveList (B x)}.

  Global Program Instance ExhaustiveHList : ExhaustiveList (hlist B l).
  Admit Obligations.

  Variable NoDup_EL : forall x (x_l : In x l), NoDup (EL _ x_l).

  Lemma NoDup_ExhaustiveHList : NoDup ExhaustiveHList.
  Proof.
  Admitted.

End ExhaustiveHList.
