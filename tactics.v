Require Export Coq.omega.Omega.
Require Import Coq.Bool.Bool.
Require Export Coq.Classes.EquivDec.
Require Export Coq.Program.Program.
Require Export Coq.Setoids.Setoid.

(** * A bunch of useful tactics (and abbreviations). *)

(** Varia *)

Ltac ref := reflexivity.

Ltac hyp := assumption.

Ltac sym := symmetry.

Ltac arith_contr := elimtype False; omega.

Ltac ded h := generalize h; intro.

Ltac ssimpl := simpl in *; try subst. 

Ltac easy := ssimpl; auto.

(** Cleaning the proof context *)

Ltac remove_dup_hyps := repeat
  match goal with
  | H: ?X, H': ?X |- _ => clear H'
  end.

Ltac clear_all := repeat
  match goal with
  | H: _ |- _ => clear H
  end.

Ltac remove_trivial_equalities := repeat
  match goal with
  | H: ?X = ?X |- _ => clear H
  end.

Ltac clean := remove_trivial_equalities; remove_dup_hyps.

(** Equality simplification *)

Require Import Coq.Classes.Equivalence.

Ltac simpl_eq :=
  match goal with
  | H: ?X = ?X |- _ => clear H
  | H: _ = _ |- _ => progress (simplify_eq H; intros; try subst; remove_dup_hyps)
  | H: _ === _ |- _ => rewrite H; clear H
  end.

Ltac simpl_eqs := repeat simpl_eq.

(** Hypothesis decomposition *)

Ltac decomp_hyp H := 
  match type of H with
  | _ /\ _ => decompose [and] H; clear H
  | _ \/ _ => decompose [or] H; clear H
  | ex _ => decompose [ex] H; clear H
  | sig _ => decompose record H; clear H
  end.

Ltac decomp :=
  repeat
    match goal with
    | H: _ |- _ => decomp_hyp H
    end.

(** Dependent rewriting *)

Ltac dep_rewrite :=
  match goal with
  | H : existT ?A ?a ?b = existT ?A ?a ?c |- _ => 
      let eq := fresh "eq" in
        set (eq := inj_pairT2 _ A _ _ _ H); clearbody eq; rewrite eq in *; clean
  | H : ?x = _ |- _ => subst x
  | H : _ = ?x |- _ => subst x
  end.

Ltac dep_subst := repeat progress (clean; try dep_rewrite; try subst).

(** Inversion *)

Ltac invert H := inversion H; try subst.

Ltac dep_invert H := inversion H; dep_subst.

(** Boolean simplifications *)

Ltac bool_case :=
  repeat progress (bool_simpl ||
    match goal with
    | H: ?X || ?Y = true |- _ => destruct (orb_true_elim _ _ H); clear H
    end)

with bool_solve := 
  repeat split; intros; bool_simpl; decomp; try solve [hyp | bool_case; auto]

with bool_simpl :=
  repeat
    match goal with
    | H: ?X && ?Y = true |- _ => destruct (proj1 (andb_true_iff X Y) H); clear H
    | |- ?X && ?Y = true => apply andb_true_intro; split
    | |- ?X || ?Y = true => apply orb_true_intro
    | |- context [?X && ?Y = true] => 
           setoid_replace (X && Y = true) with (X = true /\ Y = true) by bool_solve
    | |- context [?X || ?Y = true] => 
           setoid_replace (X || Y = true) with (X = true \/ Y = true) by bool_solve
    end.

(* FIXME, this should go somewhere else but where? *)
Notation "()" := tt.

Ltac crunch :=
  let intuition_ext := simpl in *; intuition eauto with datatypes; try subst; decomp; dep_subst; try congruence in
  let solve_arith := try omega; try (elimtype False; omega) in
    repeat progress intuition_ext; solve_arith.

Ltac dep_destruct E :=
  let x := fresh "x" in
    remember E as x; simpl in x; dependent destruction x;
      try match goal with
            | [ H : _ = E |- _ ] => rewrite <- H in *; clear H
          end.
