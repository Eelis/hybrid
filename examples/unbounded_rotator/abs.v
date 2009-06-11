Require Import util list_util c_util.
Require Import bnat.
Require Import geometry.
Require Import monotonic_flow.
Require Import hs_solver.
Require decreasing_exponential_flow.
Require abstract abstraction square_abstraction interval_spec.
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

Definition ap: abstract.Parameters system :=
  square_abstraction.ap (NoDup_bnats 5) (NoDup_bnats 5)
  Interval_bounds Interval_bounds _ _ _ _ _ _ _ _ _ xinterval yinterval.

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

Let initial_dec := @square_abstraction.initial_dec
  _ _ _ _ _ _ _ _ _ (NoDup_bnats 5) (NoDup_bnats 5)
  Interval_bounds Interval_bounds _ _ _ _ initial_invariant _ _ invariant_wd NoDup_locations
  xinterval yinterval
  _ _ initial_representative.

Obligation Tactic := idtac.

(* Abstract invariant *)

Program Definition invariant_dec (eps: Qpos) (li : Location * abstract.Region ap):
    overestimation (square_abstraction.abstract_invariant li) := true.

Next Obligation. intros. discriminate. Qed.

(* Abstract guard *)

Definition guard_square (l l': Location): option OpenSquare :=
  match l, l' with
  | Up, Right   => Some (unbounded_range, above ('(41#10)))
  | Right, Down => Some (above ('(41#10)), unbounded_range)
  | Down, Left  => Some (unbounded_range, below ('(9#10)))
  | Left, Up    => Some (below ('(9#10)), unbounded_range)
  | _, _ => None
  end.

Lemma guard_squares_correct: forall s l',
  concrete.guard system s l' <->
  match guard_square (loc s) l' with
  | None => False
  | Some v => in_osquare (point s) v
  end.
Proof.
  destruct s as [l [xv yv]].
  destruct l; destruct l'; repeat split; simpl; auto; intros [[A B] [C D]]; auto.
Qed.

Let guard_dec: Qpos -> forall l (r : abstract.Region ap) l',
  overestimation (square_abstraction.abstract_guard l r l')
   := square_abstraction.guard_dec guard_square guard_squares_correct.

(* Abstract discrete transitions *)

Program Definition disc_trans_dec eps := square_abstraction.disc_trans
  (invariant_dec eps) xreset yreset _ (guard_dec eps) eps.
Next Obligation. reflexivity. Qed.

(* Abstract continuous transitions *)

Definition hints (l : Location) (r r' : abstract.Region ap) (i: r <> r'): option (abstraction.AltHint ap l r r') := None.

Let cont_trans eps := abstraction.cont_trans
  (@abstraction.dealt_hints _ ap hints)
  (square_abstraction.cont_trans_cond_dec
  x_flow_inv y_flow_inv x_rfis y_rfis
  invariant_squares invariant_squares_correct eps).

(* Abstract system *)

Definition system (eps: Qpos): abstract.System ap :=
  abstract.Build_System (initial_dec eps) (disc_trans_dec eps) (cont_trans eps).

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
    sig (fun ss: list (abstract.State conc.system (abstract.Region ap)) =>
    LazyProp (forall s, unsafe s -> forall r, abstract.abs ap s r -> In r ss))
      := square_abstraction.unsafe_abstract
        (NoDup_bnats 5) (NoDup_bnats 5)
        Interval_bounds Interval_bounds xinterval yinterval
        unsafe _ unsafe_squares_representative.
