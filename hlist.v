Require Export hybrid.tactics.
Require Export hybrid.util.
Require Import hybrid.list_util.
Require Export Coq.Lists.List.
Require Export Coq.Classes.EquivDec.
Require Import Coq.Logic.Eqdep_dec.

Set Implicit Arguments.

(** * Heterogenous lists *)

Section hlists_def.

  Context `{B : A -> Type}.

  (* heterogenous list parametrized by 'list signature' *)
  Inductive hlist : list A -> Type :=
  | HNil : hlist nil
  | HCons : forall x xs, B x -> hlist xs -> hlist (x::xs)
  .

End hlists_def.

Implicit Arguments HNil [A B].
Implicit Arguments HCons [A B x xs].

Infix ":::" := HCons (right associativity, at level 60).

Ltac hlist_simpl :=
  repeat 
    match goal with
    | hl : hlist [] |- _ => dep_destruct hl
    | hl : hlist (_::_) |- _ => dep_destruct hl
    | H : _:::_ = _:::_ |- _ => inversion H; clear H
    end.

 (** [hget] on [HList]s is similar to [Vnth] on [vector]s *)
Section hlist_get.

  Context `{B : A -> Type, elt : A}.

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

(** Decidability of Leibniz equality on [HList]s (given deecidable 
    equality on all types of its elements). *)
Section hlist_eqdec.

  Context `{B : A -> Type, lt : list A}.
  Variable EltsEqDec : forall x, In x lt -> EqDec (B x) eq.

  Lemma hlist_eq_fst_eq a lt (x y : B a) (xs ys : hlist lt) :
    x:::xs === y:::ys ->
    x === y.
  Proof.
    inversion 1; dep_subst; intuition.
  Qed.

  Lemma hlist_eq_snd_eq a lt (x y : B a) (xs ys : hlist lt) :
    x:::xs === y:::ys ->
    xs === ys.
  Proof.
    inversion 1; dep_subst; intuition.
  Qed.

  Global Hint Resolve hlist_eq_fst_eq hlist_eq_snd_eq.

  Global Program Instance hlist_EqDec : EqDec (hlist (B:=B) lt) eq.
  Next Obligation.
    revert x y; induction lt; intros; hlist_simpl; crunch;
      match goal with
      | EQ : forall x, ?a = x \/ In x ?l -> _, x : B ?a, y : B ?a 
          |- context [?x:::_ === ?y:::_] =>
          let a_al0 := fresh "a_al0" in
          assert (a_al0 : In a (a :: l)) by intuition;
          destruct (EQ a a_al0 x y)
      end;
      match goal with
      | IH : (forall x, In x ?l -> EqDec (?B x) eq) -> forall x y, {x === y} + {x =/= y} 
          |- context [_:::?xs === _:::?ys] =>
          let IHpre := fresh "IHpre" in
          assert (IHpre : forall x, In x l -> EqDec (B x) eq) by intuition;
          destruct (IH IHpre xs ys)
      end;
      simpl_eqs; crunch; compute; crunch.
  Qed.

End hlist_eqdec.

Section hlist_funs.

  Variables (A : Type) (B : A -> Type) (lt : list A).
(* FIXME, using instead the Context below gives a wrong type for hbuild,
          as [lt] is unneccessarily abstracted in it. This problem with
          Context is fixed in 8.3 *)
(*  Context `{B : A -> Type}{lt : list A}.*)

  (** [hsingleton x] is a [HList] with only one element [x] *)
  Definition hsingleton (t : A) (x : B t) : hlist [t] := x:::HNil.

  (** [hhd] of [x::xs] is [x] *)
  Definition hhd (l : hlist lt) :=
    match l in hlist lt
      return match lt with
             | nil => unit
             | x::_ => B x
             end
    with
    | HNil => tt
    | HCons _ _ x _ => x
    end.

  (** [htl] of [x::xs] is [xs] *)
  Definition htl (l : hlist (B:=B) lt) :=
    match l in hlist lt
      return match lt with
             | nil => unit
             | _ :: lt' => hlist lt'
             end 
    with
    | HNil => tt
    | HCons _ _ _ tl => tl
    end.

  (** [happ [x_1; ... x_n] [y_1; ... y_n] = [x_1; ... x_n; y_1; ... y_n]] *)
  Fixpoint happ (lt1 : list A) (l1 : hlist (B:=B) lt1) : 
    forall lt2, hlist lt2 -> hlist (lt1 ++ lt2) :=
    match l1 in hlist lt1 
      return forall lt2, hlist lt2 -> hlist (lt1 ++ lt2) 
    with
    | HNil => fun _ l2 => l2
    | HCons _ _ x l1' => fun _ l2 => HCons x (happ l1' l2)
    end.

  Variable f : forall x, B x.

  (** [hbuild [t_1; ... t_n] = [f t_1; ... f t_n]] *)
  Fixpoint hbuild (lt : list A) : hlist lt :=
    match lt with
    | nil => HNil
    | x::lt' => HCons (f x) (hbuild lt')
    end.

End hlist_funs.

Infix "+++" := happ (right associativity, at level 60).

Section HList_prods.

  Context `{B : A -> Type}.

  (* [hlist_combine [x_1; ... x_n] [ys_1; ... ys_n] = 
     [x_1::ys_1; ... x_n::ys_n; x_2::ys_1 ... x_n::ys_n]] *)
  Fixpoint hlist_combine t (lt : list A) 
    (xl : list (B t)) (ys : list (hlist lt)) : list (hlist (t::lt)) :=
    match xl with
    | [] => []
    | x::xs => map (fun y_i => x:::y_i) ys ++ hlist_combine xs ys
    end.

  Lemma hlist_combine_In a lt (x : B a) (ys : hlist lt) all_x all_ys : 
    In x all_x -> In ys all_ys ->
    In (x:::ys) (hlist_combine all_x all_ys).
  Proof.
    induction all_x; crunch.
  Qed.

  Ltac NoDup_simpl :=
    repeat
      match goal with
      | |- NoDup (_ ++ _) => apply NoDup_app
      | |- NoDup (map _ _) => apply NoDup_map
      | H : NoDup (_::_) |- _ => inversion H; clear H
      end.

  Ltac list_simpl :=
    repeat 
      match goal with
      | H : In _ (?l ++ ?m) |- _ => 
          destruct (in_app_or l m _ H); clear H
      | H : In _ (map _ _) |- _ => 
          destruct (proj1 (in_map_iff _ _ _) H); clear H
      end.

  Lemma hlist_combine_hd a lt (x : hlist (a :: lt)) xs ys :
    In x (hlist_combine xs ys) ->
    In (hhd x) xs.
  Proof.
    induction xs; repeat (hlist_simpl; crunch; list_simpl).
  Qed.

  Lemma map_In_head a lt (x : hlist (a::lt)) (el : B a) xs :
    In x (map (fun tail => el ::: tail) xs) ->
    hhd x = el.
  Proof.
    repeat (list_simpl; crunch).
  Qed.

  Hint Resolve hlist_combine_hd map_In_head.

  Lemma hlist_combine_NoDup (a : A) lt all_x all_ys : 
    NoDup all_x -> NoDup all_ys ->
    NoDup (hlist_combine (t:=a)(lt:=lt) all_x all_ys).
  Proof.
    induction all_x; 
      repeat progress
        (crunch; hlist_simpl; NoDup_simpl;
         try
           match goal with
           | H : In ?x (map (fun _ => ?elt ::: _) _) |- _ =>
               assert (hhd x = elt) by crunch
           end
        ).
  Qed.

  Fixpoint hlist_prod_tuple (lt : list A) (l : hlist (B := fun T => list (B T)) lt)
    : list (hlist lt) :=
    match l in hlist lt return list (hlist lt) with
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

  Context {EL : forall x, ExhaustiveList (B x)}.

  Program Instance ExhaustiveHList : ExhaustiveList (hlist l) :=
    { exhaustive_list := 
        hlist_prod_tuple (hbuild _ (fun x => @exhaustive_list _ (EL x)) l)
    }.
  Next Obligation.
    induction x; crunch; apply hlist_combine_In; crunch.
  Qed.

  Variable NoDup_EL : forall x, NoDup (EL x).

  Hint Constructors NoDup.
  Hint Resolve @hlist_combine_NoDup.

  Lemma NoDup_ExhaustiveHList : NoDup ExhaustiveHList.
  Proof.
    simpl; induction l; crunch.
  Qed.

End ExhaustiveHList.
