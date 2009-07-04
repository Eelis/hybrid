Require Import List util Ensembles list_util stability geometry
  monotonic_flow concrete hs_solver.
Require square_abstraction.
Set Implicit Arguments.

(* Locations *)

Inductive Location: Set := Up | Right | Down | Left.

Instance Location_eq_dec: EquivDec.EqDec Location eq.
Proof. hs_solver. Defined.

Instance locations: ExhaustiveList Location :=
  { exhaustive_list := Up :: Right :: Down :: Left :: nil }.
Proof. hs_solver. Defined.

Lemma NoDup_locations: NoDup locations.
Proof. hs_solver. Qed.

(* States *)

Let Point := geometry.Point.
Let State : Type := (Location * Point)%type.

Definition point: State -> Point := snd.
Definition loc: State -> Location := fst.
Definition x: State -> CR := fst ∘ point.
Definition y: State -> CR := snd ∘ point.

(* Invariant *)

Definition invariant (s: State): Prop := True.

Lemma invariant_wd: forall l l', l = l' ->
  forall (p p': Point), p[=]p' -> (invariant (l, p) <-> invariant (l', p')).
Proof. split; trivial. Qed.

(* Initial *)

Open Local Scope CR_scope.

Definition initial (s: State): Prop :=
  loc s = Up /\ '0 <= x s /\ x s <= '(9#10).

Definition initial_invariant s: initial s -> invariant s
  := fun _ => I.

(* Flow *)

Definition xf (l: Location): Flow CRasCSetoid :=
  match l with
  | Right => flow.positive_linear.f
  | Left => flow.negative_linear.f
  | _ => flow.constant.flow
  end.

Definition yf (l: Location): Flow CRasCSetoid :=
  match l with
  | Up => flow.positive_linear.f
  | Down => flow.negative_linear.f
  | _ => flow.constant.flow
  end.

(* Reset *)

Definition xreset (l l': Location): square_abstraction.Reset :=
  square_abstraction.Reset_id.
Definition yreset (l l': Location): square_abstraction.Reset :=
  square_abstraction.Reset_id.

Definition reset (l l': Location) (p: Point): Point :=
  ( square_abstraction.apply_Reset (xreset l l') (fst p)
  , square_abstraction.apply_Reset (yreset l l') (snd p)).

Definition world: OpenSquare := unbounded_square.

Definition invariant_squares (l: Location): OpenSquare := unbounded_square.

Lemma invariant_squares_correct (l : Location) (p : Point):
  invariant (l, p) -> in_osquare p (invariant_squares l).
Proof. intros. apply in_unbounded_square. Qed.

(* Guard *)

Definition guard (s: State) (l: Location): Prop :=
  match loc s, l with
  | Up, Right   => '(41#10) <= y s
  | Right, Down => '(41#10) <= x s
  | Down, Left  => y s <= '(9#10)
  | Left, Up    => x s <= '(9#10)
  | _, _ => False
  end.

(* Concrete system itself *)

Lemma invariant_stable (l: Location) (p: Point) (t: Time):
  stability.Stable (invariant (l, (fun l0 : Location => product_flow (xf l0) (yf l0)) l p t)).
Proof. auto. Qed.

Definition system: System :=
  Build_System
    _ _
    NoDup_locations
    initial
    initial_invariant
    invariant_wd
    (fun l => product_flow (xf l) (yf l))
    invariant_stable
    guard
    reset.

(* Safety *)

  Definition unsafe: Ensemble (concrete.State system)
    := fun s =>
        '2 <= x s /\ x s <= '3 /\
        '2 <= y s /\ y s <= '3.

  Definition UnsafeUnreachable: Prop := unsafe ⊆ unreachable.
    (* This is proved in safe.v. *)

  (* We can also phrase the property less negatively: *)

  Definition safe := Complement unsafe.

  Definition ReachablesSafe: Prop := reachable ⊆ safe.

  (* Of course, the negative version implies the positive one: *)

  Goal UnsafeUnreachable -> ReachablesSafe.
  Proof. intros H s A B. apply H with s; assumption. Qed.
