Require Import hybrid.hypergeometry.
Require Import hybrid.util.
Require Import hybrid.c_util.
Require Import hybrid.hlist_aux.
Require Import hybrid.square_abstraction.
Require Import hybrid.vector_setoid.
Require Import hybrid.monotonic_flow.
Require Import hybrid.stability.

Require Import CoLoR.Util.Vector.VecUtil.

Set Implicit Arguments.

Open Scope CR_scope.

Section contents.

  (* Let's fix a dimension *)

  Variable n : nat.

  Definition forallDim (F : forall i, (i < n)%nat -> Type) := 
    forall i (ip : (i < n)%nat), F i ip.

  (* If one has a concrete hybrid system.. *)

  Variable chs : concrete.System.

  (* .. and points in that system basically correspond to points in the plane.. *)

  Notation proj_morpher := 
    (morpher (@st_eq (concrete.Point chs) ==> @st_eq CRasCSetoid)%signature).

  Variable proj : vector proj_morpher n.

  Hypothesis xyp : HyperPoint n -> concrete.Point chs.
  
  Definition pxy (p : concrete.Point chs) : HyperPoint n :=
    Vmap (fun pi : proj_morpher => pi p) proj.

  Hypotheses
    (xyp_pxy: forall p, xyp (pxy p) = p)
      (* TODO: should we split this condition into separate dimensions, like in square_abstraction? *)
    (pxy_xyp: forall p, pxy (xyp p) = p). 

  (* .. and flow in that system is separable over the two axes.. *)

  Variables
    (flows : concrete.Location chs -> vector (Flow CRasCSetoid) n)
    (flow_inv : concrete.Location chs -> 
      forall i (ip : (i < n)%nat), OpenRange -> OpenRange -> OpenRange)
    (flow_inv_correct : forall l,
      forallDim (fun i ip => range_flow_inv_spec (Vnth (flows l) ip) (flow_inv l ip)))
    (flow_separable : forall l p t,
      concrete.flow chs l p t = xyp (vector_flow (flows l) (pxy p) t)).

  (* .. and on both axes, abstraction parameters can be formed based on
   OpenRange regions.. *)

  Context (A : Set) (B : A -> Set).

  Context
    (intervals : vector A n)
    (intervals_eq_dec : forall x, EquivDec.EqDec (B x) eq)
    (intervals_enum : forall x, ExhaustiveList (B x))
    (intervals_NoDup : forall x, NoDup (intervals_enum x))
    (intervals_range : forallDim (fun i ip => B (Vnth intervals ip) -> OpenQRange))
    (absInterval : forall (l : concrete.Location chs) (p : concrete.Point chs), concrete.invariant (l, p) ->
      forallDim (fun i ip =>
        DN { int : B (Vnth intervals ip) | in_orange (intervals_range i ip int) (Vnth (pxy p) ip)}
    )).

  Definition ap_inv_DN :
    forall (i : nat) (ip : (i < n)%nat) (l : concrete.Location chs) (p : concrete.Point chs),
      concrete.invariant (l, p) ->
      DN {i : B (Vnth intervals ip) | in_orange (intervals_range ip i) (Vnth proj ip p)}.
  Proof.
    intros. set (w := absInterval l p H (ip:=ip)). simpl in w.
    unfold pxy in w. rewrite Vnth_map in w. exact w.
  Qed.

  Definition ap : abstract.Space chs :=
    abstract.hyper_space 
      (list_of_vec (Vbuild (fun i (ip : (i < n)%nat) =>
         interval_abstraction.space chs (Vnth proj ip) (intervals_NoDup _) (intervals_range _) (@ap_inv_DN i ip)
      ))).

  Definition region2range :
    forall (i : nat) (ip : (i < n)%nat),
      abstract.Region
        (Vnth (Vbuild (fun i (ip : (i < n)%nat) =>
          interval_abstraction.space chs (Vnth proj ip) (intervals_NoDup _) (intervals_range _) (@ap_inv_DN i ip)
        )) ip) -> OpenQRange.
  Proof.
    intros.
    rewrite Vbuild_nth in X.
    exact (intervals_range ip X).
  Defined.

  Definition square : abstract.Region ap -> OpenQHCube n :=
    hlist_map _ region2range.

  (*  .. then we can define useful things.

  For instance, we can easily make an invariant overestimator 
  (if one's invariant can be overestimated by a list of open squares): *)

  Section invariant_overestimator.

    Variable invariant_squares :
      forall l : concrete.Location chs, 
        { s : OpenHCube n | forall p, concrete.invariant (l, p) -> in_ohypercube (pxy p) s }.

    Program Definition make_invariant_overestimator : overestimator (@abstract.invariant _ ap) := _.
    Admit Obligations.
(*      fun li => overestimate_osquares_overlap eps (invariant_squares (fst li)) (square (snd li)).*)

  End invariant_overestimator.

  (* Similarly, if one's initial condition can be overestimated by
   an open square, we can make an initial_dec thingy. *)

  Section make_initial_overestimator.

    Variables
      (initial_location : concrete.Location chs)
      (initial_square : OpenHCube n)
      (initial_representative : forall s, concrete.initial s ->
        fst s = initial_location /\ in_ohypercube (pxy (snd s)) initial_square).

    Program Definition make_initial_overestimator (eps : Qpos) : overestimator (@abstract.Initial _ ap) := 
      fun s => _.
    Admit Obligations.
(*
        (overestimate_conj (overestimate_osquares_overlap eps (initial_square) (square (snd s)))
          (decision_overestimation (concrete.Location_eq_dec chs (fst s) initial_location))).
*)

  End make_initial_overestimator. 
  
  (* And similarly, if one's guard conditions can be overestimated by
  open squares, we can make a guard_dec thingy. *)

  Section make_guard_overestimator.

    Definition GuardSquare l l' := 
      { s : option (OpenHCube n) | forall p, concrete.guard chs (l, p) l' ->
          match s with
          | None => False
          | Some v => in_ohypercube (pxy p) v
          end
      }.

    Program Definition guard_dec (guard_square : forall l l', GuardSquare l l') (eps : Qpos) : 
      overestimator (@abstract.guard _ ap) := 
      _.
    Admit Obligations.
(*
      fun l r l' =>
      match guard_square l l' with
      | Some s => overestimate_osquares_overlap eps s (square r)
      | None => false
      end.
*)

  End make_guard_overestimator.  

  (* If the safety condition can be overestimated by a list of unsafe
   osquares, then we can select the unsafe abstract states automatically: *)

  Section square_safety.

    Variables
      (unsafe_concrete : concrete.State chs -> Prop)
      (unsafe_squares : concrete.Location chs -> list (OpenHCube n))
      (unsafe_squares_correct: forall s, unsafe_concrete s -> exists q,
        In q (unsafe_squares (fst s)) /\ in_ohypercube (pxy (snd s)) q)
      (eps: Qpos).

      Program Definition unsafe_abstract : abstract.CompleteCoverList ap unsafe_concrete :=
        _.
(*
      := flat_map (fun l => map (pair l) (flat_map (fun q =>
        filter (fun s => overestimate_osquares_overlap eps q (square s)) exhaustive_list
        ) (unsafe_squares l))) (concrete.locations chs).
*)
      Admit Obligations.

  End square_safety.

  (* Everything above is pretty simplistic. We now prepare for more complex
   transition overestimators, for which we will require some more stuff: *)

  Let reset_function := concrete.Location chs -> concrete.Location chs -> Reset.

  Variables
    (invariant_overestimator : overestimator (@abstract.invariant _ ap))
    (guard_decider : overestimator (@abstract.guard _ ap))
    (reset : vector reset_function n)
    (reset_components : forall p l l', 
      pxy (concrete.reset chs l l' p) = 
      Vmap2 (fun resetF => apply_Reset (resetF l l')) reset (pxy p)).

(*
  Section disc_trans_regions.

    Variables (eps: Qpos) (l l': concrete.Location chs) (r: abstract.Region ap).

    Definition map_orange' (f: sigT increasing): OpenRange -> OpenRange
      := let (_, y) := f in map_orange y.

    Definition x_regions :=
      match reset_x l l' with
      | Reset_const c => filter (fun r' => overestimate_oranges_overlap eps
        (* (map_orange' (increasing_const' c) (Xinterval_range (fst r))) (Xinterval_range r')) Xintervals *)
        (unit_range c: OpenRange) (Xinterval_range r')) Xintervals
      | Reset_map f => filter (fun r' => overestimate_oranges_overlap eps
        (map_orange' f (Xinterval_range (fst r))) (Xinterval_range r')) Xintervals
      | Reset_id => [fst r] (* x reset is id, so we can only remain in this x range *)
      end.

    Definition y_regions :=
      match reset_y l l' with
      | Reset_const c => filter (fun r' => overestimate_oranges_overlap eps
        (unit_range c: OpenRange) (Yinterval_range r')) Yintervals
      | Reset_map f => filter (fun r' => overestimate_oranges_overlap eps
        (map_orange' f (Yinterval_range (snd r))) (Yinterval_range r')) Yintervals
      | Reset_id => [snd r] (* x reset is id, so we can only remain in this x range *)
      end.

    Definition disc_trans_regions: list (abstract.Region ap)
      :=
      if overestimation_bool (guard_decider l r l') &&
          overestimation_bool (invariant_overestimator (l, r)) then
       filter (fun s => overestimation_bool (invariant_overestimator (l', s))) (cart x_regions y_regions)
     else [].

  End disc_trans_regions.

  Definition raw_disc_trans (eps: Qpos) (s: abstract.State ap): list (abstract.State ap) :=
    let (l, r) := s in
    flat_map (fun l' => map (pair l') (disc_trans_regions eps l l' r)) (concrete.locations chs).

  Lemma NoDup_disc_trans eps s: NoDup (raw_disc_trans eps s).

  Hint Resolve in_map_orange.

  Definition is_id_reset (r: Reset): bool :=
    match r with
    | Reset_id => true
    | _ => false
    end.

  Hint Unfold abstract.invariant abstract.guard.

  Lemma respects_disc (eps: Qpos) (s1 s2 : concrete.State chs):
    concrete.disc_trans s1 s2 -> forall i1, abstract.in_region ap (snd s1) i1 ->
    DN (exists i2, abstract.in_region ap (snd s2) i2 /\
    In (fst s2, i2) (raw_disc_trans eps (fst s1, i1))).

  Program Definition disc_trans: Qpos ->
    abstract.sharing_transition_overestimator ap (@concrete.disc_trans chs) := raw_disc_trans.

  Program Definition cont_trans_cond_dec eps l r r':
    overestimation (abstract.cont_trans ap l r r') :=
      square_flow_conditions.decide_practical
        (xflow_invr l) (yflow_invr l) (square r) (square r') eps &&
      invariant_overestimator (l, r) &&
      invariant_overestimator (l, r').
*)

End contents.
