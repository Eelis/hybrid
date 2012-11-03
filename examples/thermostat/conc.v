Set Automatic Coercions Import.

Require Import List Ensembles util stability flow list_util containers
  geometry hs_solver concrete.
Require decreasing_exponential_flow EquivDec.
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
Definition location: State -> Location := fst.
Definition clock: State -> CR := fst ∘ point.
Definition temp: State -> CR := snd ∘ point.

(* Invariant *)

Open Local Scope CR_scope.

Definition invariant (s: State): Prop :=
  0 <= clock s /\
  match location s with
  | Heat => temp s <= '10 /\ clock s <= '3
  | Cool => '5 <= temp s
  | Check => clock s <= 1
  end.

Lemma invariant_wd: forall l l', l = l' ->
  forall (p p': Point), p[=]p' -> (invariant (l, p) <-> invariant (l', p')).
Proof. unfold invariant. 
  admit. (* grind ltac:(destruct l').*) (* TODO *)
Qed.

Lemma invariant_stable s: Stable (invariant s).
Proof. revert s. intros [l p]. destruct l; intros; unfold invariant; simpl location; auto. Qed.

(* Initial *)

Definition initial (s: State): Prop :=
  location s = Heat /\
  '5 <= temp s /\ temp s <= '10 /\
  clock s == 0.

Lemma initial_invariant (s: State): initial s -> invariant s.
Proof. unfold initial, invariant. 
  admit. (* hs_solver. *) (* TODO *)
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

Definition reset (l l': Location) (p: Point): Point :=
  ( match l, l' with
    | Cool, Heat | Heat, Check | Check, Heat => 0
    | _, _ => fst p
    end
  , snd p).

(* Guard *)

Definition guard (s: State) (l: Location): Prop :=
  match location s, l with
  | Heat, Cool => '9 <= temp s
  | Cool, Heat => temp s <= '6
  | Heat, Check => '2 <= clock s
  | Check, Heat => '(1#2) <= clock s
  | _, _ => False
  end.

(* Concrete system itself *)

Definition system: System :=
  Build_System
  _ _
  NoDup_locations
  initial_invariant
  invariant_wd
  invariant_stable
  flow
  guard
  reset.

(* Safety *)

  Definition unsafe: Ensemble (concrete.State system) :=
    fun s => temp s <= '(45#10).

  Definition UnsafeUnreachable: Prop := unsafe ⊆ unreachable.
    (* This is proved in safe.v. *)

  (* We can also phrase the property less negatively: *)

  Definition safe := Complement unsafe.

  Definition ReachablesSafe: Prop := reachable ⊆ safe.

  (* Of course, the negative version implies the positive one: *)

  Goal UnsafeUnreachable -> ReachablesSafe.
  Proof. intros H s A B. apply H with s; assumption. Qed.
