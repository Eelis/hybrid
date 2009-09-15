Require Import util list_util c_util.
Require Import bnat.
Require Import geometry.
Require Import monotonic_flow.
Require Import hs_solver.
Require decreasing_exponential_flow.
Require abstract square_abstraction interval_spec.
Require EquivDec.

Require Import hybrid.examples.unbounded_rotator.conc.

Set Implicit Arguments.

Open Local Scope CR_scope.

(* Abstraction intervals *)

Program Definition spec: interval_spec.IntervalSpec 1 3 :=
  (interval_spec.bound 1 _
  (interval_spec.bound (19#10) _
  (interval_spec.bound (31#10) _
  (interval_spec.highest 4)))).

Definition Interval_bounds := interval_spec.bounds spec.
Definition xinterval := interval_spec.select_interval system fst_mor spec.
Definition yinterval := interval_spec.select_interval system snd_mor spec.

(* Abstraction parameters *)

Definition ap: abstract.Space system :=
  square_abstraction.ap _ _ _ (NoDup_bnats 5) (NoDup_bnats 5)
  Interval_bounds Interval_bounds xinterval yinterval.

(* Flow inverses *)

Definition x_flow_inv (l: Location) (a b: OpenRange): OpenRange :=
  match l with
  | Right => square_flow_conditions.one_axis.flow_range
    _ flow.positive_linear.inv_correct flow.positive_linear.mono a b
  | Left => square_flow_conditions.one_axis.flow_range
    _ flow.negative_linear.inv_correct flow.negative_linear.mono a b
  | _ => flow.constant.inv a b
  end.

Definition y_flow_inv (l: Location) (a b: OpenRange): OpenRange :=
  match l with
  | Up => square_flow_conditions.one_axis.flow_range
    _ flow.positive_linear.inv_correct flow.positive_linear.mono a b
  | Down => square_flow_conditions.one_axis.flow_range
    _ flow.negative_linear.inv_correct flow.negative_linear.mono a b
  | _ => flow.constant.inv a b
  end.

Lemma x_rfis l: range_flow_inv_spec (xf l) (x_flow_inv l).
Proof with auto.
  destruct l; simpl xf.
        apply flow.constant.inv_correct.
      unfold range_flow_inv_spec. intros.
      apply square_flow_conditions.one_axis.flow_range_covers with p...
    apply flow.constant.inv_correct.
  unfold range_flow_inv_spec. intros.
  apply square_flow_conditions.one_axis.flow_range_covers with p...
Qed.

Lemma y_rfis l: range_flow_inv_spec (yf l) (y_flow_inv l).
Proof with auto.
  destruct l; simpl yf.
        unfold range_flow_inv_spec. intros.
        apply square_flow_conditions.one_axis.flow_range_covers with p...
      apply flow.constant.inv_correct.
    unfold range_flow_inv_spec. intros.
    apply square_flow_conditions.one_axis.flow_range_covers with p...
  apply flow.constant.inv_correct.
Qed.

(* Abstract initial *)

Definition initial_square: OpenSquare := (below ('(9#10)), unbounded_range).
Definition initial_location := Up.

Lemma initial_representative: forall s: concrete.State system,
  concrete.initial s -> loc s = initial_location /\ in_osquare (point s) initial_square.
Proof. intros [l s] [H [H0 H1]]. repeat split; auto. Qed.

Let initial_dec := @square_abstraction.make_initial_overestimator
  _ _ _ _ _ _ _ _ _ (NoDup_bnats 5) (NoDup_bnats 5) _ _
  xinterval yinterval _ _ initial_representative.

(* Abstract invariant *)

Program Definition invariant_dec (eps: Qpos):
  overestimator (@abstract.invariant _ ap) := fun _ => true.

(* Abstract guard *)

Definition px := @fst_mor CRasCSetoid CRasCSetoid.
Definition py := @snd_mor CRasCSetoid CRasCSetoid.

Definition GuardSquare l l' := fun s: option OpenSquare =>
  forall p, concrete.guard system (l, p) l' ->
    match s with
    | None => False
    | Some v => in_osquare (square_abstraction.pxy system px py p) v
    end.
  (* todo: why can't we use square_abstraction.GuardSquare below? *)

Program Definition guard_square (l l': concrete.Location system):
   sig (GuardSquare l l') :=
  match l, l' return square_abstraction.GuardSquare system _ _ l l' with
  | Up, Right   => Some (unbounded_range, above ('(41#10)))
  | Right, Down => Some (above ('(41#10)), unbounded_range)
  | Down, Left  => Some (unbounded_range, below ('(9#10)))
  | Left, Up    => Some (below ('(9#10)), unbounded_range)
  | _, _ => None
  end.

Let guard_dec: Qpos -> overestimator (abstract.guard ap)
   := square_abstraction.guard_dec guard_square.

(* Abstract discrete transitions *)

Program Definition disc_trans_dec eps := square_abstraction.disc_trans
  _ _ _ _ (invariant_dec eps)  (guard_dec eps) xreset yreset _ eps.

(* Abstract continuous transitions *)

Definition hints (l : Location) (r r' : abstract.Region ap) (i: r <> r'):
  option (abstract_cont_trans_over.strong_redundant ap l i) := None.

Program Let cont_trans eps := abstract_cont_trans_over.cont_trans
  (square_abstraction.cont_trans_cond_dec
    (@id (concrete.Point system)) _ _ _ _
  x_flow_inv y_flow_inv x_rfis y_rfis
  _ (invariant_dec eps) eps)
  (@abstract_cont_trans_over.weaken_hints _ ap hints).

(* Abstract system *)

Definition system (eps: Qpos): abstract.System ap :=
  abstract.Build_System (initial_dec eps) (disc_trans_dec eps) (abstract_cont_trans_over.cont_sharing_overestimator_from_substantial_overestimator (cont_trans eps)).

(* Abstract safety *)

  (* The concrete unsafety condition was specified as a predicate on
   concrete states. Our task is to come up with a list of corresponding abstract
   states. The square_abstraction module can generate this list if we can
   overestimate the concrete unsafety condition with a list of open squares, which
   we can. So let us define these, first. *)

  Obligation Tactic := Qle_constants.
  Program Definition centre_square: OpenSquare :=
    ((2, 3): QRange, (2, 3): QRange).

  Definition unsafe_squares (l: Location): list OpenSquare := centre_square :: nil.

  (* Of course, we must prove that these actually cover the unsafe
  concrete states: *)

  Definition unsafe_squares_representative s: unsafe s ->
    exists q, In q (unsafe_squares (fst s)) /\ in_osquare (snd s) q.
  Proof.
    unfold unsafe. intuition.
    exists centre_square.
    simpl. repeat split; auto.
  Qed.

  (* We can now invoke square_abstraction's unsafe_abstract to obtain a list
  of abstract states that cover the unsafe concrete states. This list will be a key
  ingredient in safe.v. *)

  Definition unsafe_abstract: Qpos ->
    sig (fun ss: list (abstract.State ap) =>
    LazyProp (forall s, unsafe s -> forall r, abstract.abs s r -> In r ss))
      := square_abstraction.unsafe_abstract
        (NoDup_bnats 5) (NoDup_bnats 5)
        Interval_bounds Interval_bounds xinterval yinterval
        unsafe _ unsafe_squares_representative.
