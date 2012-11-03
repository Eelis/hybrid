Require Export hybrid.tactics.
Require Export hybrid.util.
Require Import hybrid.list_util.
Require Export Coq.Lists.List.
Require Export Coq.Program.Program.
Require Import CoLoR.Util.Vector.VecUtil.

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

  Context {A} `{B : A -> Type}.

  Inductive hlist (l : list A) : Type :=
  | HNil : forall `{l = nil}, hlist l
  | HCons : forall `{H : nil <> l}, B (head H) -> hlist (tail l) -> hlist l.

End hlists_def.

Notation "'hnil'" := (HNil (H:=refl_equal _)).
Notation "x ::: xs" := (HCons (H:=@nil_cons _ _ _) x xs) (at level 60).

Section hlists_funs.

(* FIXME, use context when switching to 8.3
  Context `{B : A -> Type, l : list A, a : A}.
*)
  Variable (A : Type) (B : A -> Type) (l : list A) (a : A).

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

  (** [hsingleton x] is a [HList] with only one element [x] *)
  Definition hsingleton (t : A) (x : B t) : hlist [t] := x:::hnil.

  Variable f : forall x, B x.

  (** [hbuild [t_1; ... t_n] = [f t_1; ... f t_n]] *)
  Fixpoint hbuild (lt : list A) : hlist lt :=
    match lt with
    | nil => hnil
    | x::lt' => f x ::: hbuild lt'
    end.

End hlists_funs.

Ltac hlist_simpl :=
  repeat 
    match goal with
    | hl : hlist [] |- _ => dep_destruct hl
    | hl : hlist (_::_) |- _ => dep_destruct hl
    | H : _:::_ = _:::_ |- _ => inversion H; clear H
    end.

(** Decidability of Leibniz equality on [hlist]s (given deecidable 
    equality on all types of its elements). *)
Section hlist_eqdec.

  Context {A} `{B : A -> Type, lt : list A}.
  Variable EltsEqDec : forall x, In x lt -> EqDec (B x) eq.

  Lemma hlist_eq_fst_eq a (x y : B a) (xs ys : hlist lt) :
    x:::xs === y:::ys ->
    x === y.
  Proof.
    inversion 1; dep_subst; intuition.
  Qed.

  Lemma hlist_eq_snd_eq a (x y : B a) (xs ys : hlist lt) :
    x:::xs === y:::ys ->
    xs === ys.
  Proof.
    inversion 1; dep_subst; intuition.
  Qed.

  Global Program Instance hlist_EqDec : EqDec (hlist (B:=B) lt) eq.
  Next Obligation.
(*
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
*)
  Admitted.

End hlist_eqdec.

Global Hint Resolve hlist_eq_fst_eq hlist_eq_snd_eq.

Section HList_prods.

  Context {A} `{B : A -> Type}.

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

  Lemma hlist_combine_hd a lt (x : hlist (a :: lt)) xs ys :
    In x (hlist_combine xs ys) ->
    In (hhd x) xs.
  Proof.
  Admitted.
  (*  induction xs; repeat (hlist_simpl; crunch; list_simpl).
  Qed. *)

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
  Admitted. (*
    induction all_x; 
      repeat progress
        (crunch; hlist_simpl; NoDup_simpl;
         try
           match goal with
           | H : In ?x (map (fun _ => ?elt ::: _) _) |- _ =>
               assert (hhd x = elt) by crunch
           end
        ).
  Qed. *)

  Program Fixpoint hlist_prod_tuple (lt : list A) (l : hlist (B := fun T => list (B T)) lt) :
    list (hlist (B:=B) lt) :=
    match lt with
    | [] => [hnil]
    | t::ts => 
        match l with
        | HNil _ => !
        | HCons _ x xs =>
            let w := @hlist_prod_tuple _ xs in _
        end
    end.
   (* FIXME, this is akward... get rid of the obligation *)
  Next Obligation.
  Proof.
    admit.
    (* exact (@hlist_combine t ts x (hlist_prod_tuple _ xs)). *)
  Defined.

End HList_prods.

Section ExhaustiveHList.

  Variable A : Type.
  Variable B : A -> Type.
  Variable l : list A.

  Context {EL : forall x, ExhaustiveList (B x)}.

  Global Program Instance ExhaustiveHList : ExhaustiveList (hlist l) :=
    { exhaustive_list := 
        hlist_prod_tuple (hbuild _ (fun x => @exhaustive_list _ (EL x)) l)
    }.
  Next Obligation.
  Admitted.

  Variable NoDup_EL : forall x, NoDup (EL x).

  Hint Constructors NoDup.
  Hint Resolve @hlist_combine_NoDup.

  Lemma NoDup_ExhaustiveHList : NoDup ExhaustiveHList.
  Proof.
    simpl; induction l; crunch.
    admit.
  Qed.

End ExhaustiveHList.

Section hlist_map.

  Variable A C : Type.
  Variable B : A -> Type.
  Variable n : nat.
  Variable l : vector A n.
  (*Variable f : forall i (ip : (i < n)%nat), B (Vnth l ip) -> C.*)

  Definition hlist_map (f : forall i (ip : (i < n)%nat), B (Vnth l ip) -> C) :
    hlist (B:=B) (list_of_vec l) -> 
    vector C n.
  Proof.
  Admitted.

End hlist_map.
