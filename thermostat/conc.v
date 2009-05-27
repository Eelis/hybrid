Require Import List.
Require Import util.
Require Import list_util.
Require Import geometry.
Require Import hs_solver.
Require decreasing_exponential_flow.
Require Import concrete.
Require EquivDec.
Set Implicit Arguments.

Module dec_exp_flow := decreasing_exponential_flow.

(* Locations *)

Inductive Location: Set := Heat | Cool | Check.

Instance Location_eq_dec: EquivDec.EqDec Location eq.
Proof. hs_solver. Defined.

Instance locations: ExhaustiveList Location :=
  { exhaustive_list := Heat :: Cool :: Check :: nil }.
Proof. hs_solver. Defined.

Lemma NoDup_locations: NoDup locations.
Proof. hs_solver. Qed.

(* States *)

Let Point := geometry.Point.
Let State : Type := (Location * Point)%type.

Definition point: State -> Point := snd.
Definition loc: State -> Location := fst.
Definition clock: State -> CR := fst ∘ point.
Definition temp: State -> CR := snd ∘ point.

(* Invariant *)

Open Local Scope CR_scope.

Definition invariant (s: State): Prop :=
  '0 <= clock s /\
  match loc s with
  | Heat => temp s <= '10 /\ clock s <= '3
  | Cool => '5 <= temp s
  | Check => clock s <= '1
  end.

Lemma invariant_wd: forall l l', l = l' ->
  forall (p p': Point), p[=]p' -> (invariant (l, p) <-> invariant (l', p')).
Proof.
  unfold invariant. grind ltac:(destruct l').
Qed.

(* Initial state *)

Definition initial (s: State): Prop :=
  loc s = Heat /\
  '5 <= temp s /\ temp s <= '10 /\
  clock s == '0.

Lemma initial_invariant (s: State): initial s -> invariant s.
Proof.
  unfold initial, invariant.
  hs_solver.
Qed.

(* Flow *)

Definition clock_flow (l: Location): Flow CRasCSetoid := flow.positive_linear.f.

Definition temp_flow (l: Location): Flow CRasCSetoid :=
  match l with
  | Heat => flow.scale.flow ('2) flow.positive_linear.f
  | Cool => dec_exp_flow.f
  | Check => flow.scale.flow ('(1#2)) dec_exp_flow.f
  end.

Definition flow l := product_flow (clock_flow l) (temp_flow l).

(* Reset *)

Definition clock_reset (l l': Location): square_abstraction.Reset :=
  match l, l' with
  | Cool, Heat | Heat, Check | Check, Heat => square_abstraction.Reset_const ('0)
  | _, _ => square_abstraction.Reset_id (* dummy *)
  end.

Definition temp_reset (l l': Location): square_abstraction.Reset :=
  square_abstraction.Reset_id. (* dummy *)

Definition reset (l l': Location) (p: Point): Point :=
  ( square_abstraction.apply_Reset (clock_reset l l') (fst p)
  , square_abstraction.apply_Reset (temp_reset l l') (snd p)).

(* Guard *)

Definition guard (s: State) (l: Location): Prop :=
  match loc s, l with
  | Heat, Cool => '9 <= temp s
  | Cool, Heat => temp s <= '6
  | Heat, Check => '2 <= clock s
  | Check, Heat => '(1#2) <= clock s
  | _, _ => False
  end.

(* Concrete system *)

Definition system: System :=
  Build_System _ _ NoDup_locations initial invariant
  initial_invariant invariant_wd flow guard reset.

Definition state_unsafe (s: State): Prop := temp s <= '(45#10).
